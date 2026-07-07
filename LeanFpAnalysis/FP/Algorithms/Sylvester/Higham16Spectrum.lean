-- Algorithms/Sylvester/Higham16Spectrum.lean
--
-- Constructive spectral directions for the vec/Kronecker Sylvester
-- coefficient (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., Chapter 16.1, equation (16.3)) and the Bartels-Stewart
-- supplied-triangular column recurrence (Higham, 2nd ed., Chapter 16.2,
-- equations (16.4)-(16.8)).  This file complements `Higham16.lean`, whose
-- namespace and matrix conventions it follows exactly; it adds the general
-- (non-diagonal) constructive halves of those two source rows:
--
-- * every pairwise difference of supplied real eigenpairs of `A` and `B^T`
--   is an eigenvalue of `I_n kron A - B^T kron I_m`, and a shared eigenvalue
--   makes the coefficient singular (the constructive directions of (16.3));
-- * with a SUPPLIED upper-triangular `T`, the transformed equation
--   `AX - XT = C` decouples column by column into
--   `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`, and per-column
--   nonsingularity of the shifted matrices gives a unique exact solution by
--   forward substitution over columns; this is the (16.5)/(16.6)
--   Bartels-Stewart existence statement at the supplied-factor level.
--
-- Honest scope:
-- * The complex Schur route is imported to prove determinant nonsingularity
--   of the real vec/Kronecker coefficient from a supplied no-common complex
--   right-eigenpair hypothesis on the entrywise complexifications of `A` and
--   `B`.  The full spectrum-characterization statement -- every eigenvalue of
--   the Kronecker coefficient is a difference `lam_i(A) - mu_j(B)` -- is still
--   not stated as a complete iff here.
-- * The quasi-triangular (2x2 diagonal block, real-Schur) Bartels-Stewart
--   route behind equations (16.4), (16.7), and (16.8) is represented by an
--   imported real quasi-Schur existence wrapper plus supplied adjacent
--   two-column exact block-equation lemmas; the full block solver and
--   floating-point error propagation remain open.
-- * No floating-point rounding analysis: triangular and eigenpair data in the
--   solver wrappers are supplied hypotheses, exactly as in the supplied-factor
--   diagonal case of `Higham16.lean`.

import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16
import LeanFpAnalysis.FP.Analysis.SylvesterSchurExistence
import LeanFpAnalysis.FP.Analysis.RealQuasiSchur
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- (16.4): real quasi-Schur factors for both Sylvester sides
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), real Schur form
    packaged for the Sylvester equation: both real square factors have
    orthogonal changes of basis to real quasi-upper-triangular factors, with
    explicit block maps whose fibers have size at most two.  This is only the
    exact real quasi-Schur existence step used before the Bartels-Stewart
    recurrence; it does not assert the block solve, nonsingularity of the
    resulting Sylvester coefficient, or any floating-point stability bound. -/
theorem sylvester_realQuasiSchur_factors (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    ∃ (U R : Matrix (Fin m) (Fin m) Real)
      (V S : Matrix (Fin n) (Fin n) Real)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      U ∈ Matrix.orthogonalGroup (Fin m) Real ∧
      V ∈ Matrix.orthogonalGroup (Fin n) Real ∧
      Matrix.transpose U * Matrix.of A * U = R ∧
      Matrix.transpose V * Matrix.of B * V = S ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) := by
  obtain ⟨U, pA, hU, hpAmono, hpAcard, hAzero⟩ :=
    real_quasi_schur_blocks (Matrix.of A)
  obtain ⟨V, pB, hV, hpBmono, hpBcard, hBzero⟩ :=
    real_quasi_schur_blocks (Matrix.of B)
  refine ⟨U, Matrix.transpose U * Matrix.of A * U,
    V, Matrix.transpose V * Matrix.of B * V, pA, pB,
    hU, hV, rfl, rfl, hpAmono, hpAcard, ?_, hpBmono, hpBcard, ?_⟩
  · intro i j hij
    exact hAzero i j hij
  · intro i j hij
    exact hBzero i j hij

/-- Adapter from Mathlib's orthogonal-group predicate to the repository's
    function-matrix orthogonality predicate. -/
theorem IsOrthogonal.of_mem_orthogonalGroup {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) Real) :
    IsOrthogonal n (fun i j => Q i j) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  rw [Matrix.mem_orthogonalGroup_iff'] at hQ
  have hentry := congrFun (congrFun hQ i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.5), real
    quasi-Schur existence combined with the exact Schur-coordinate Sylvester
    equivalence.  The theorem chooses real quasi-Schur factors for `A` and `B`,
    repackages them in the legacy function-matrix interface, and immediately
    exposes the exact equivalence between the original equation and the
    Schur-coordinate equation.

    Scope: this is only the exact coordinate-transform bridge.  It does not
    assert structural nonsingularity of the quasi-triangular block systems, a
    Hessenberg-Schur reduction, a full Bartels-Stewart solve, or any
    floating-point stability bound. -/
theorem sylvester_realQuasiSchur_transform_solution_iff (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Y : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      (IsSylvesterSolutionRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V))) <->
        IsSylvesterSolutionRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) := by
  obtain ⟨Umat, pA, hUmat, hpAmono, hpAcard, hAzero⟩ :=
    real_quasi_schur_blocks (Matrix.of A)
  obtain ⟨Vmat, pB, hVmat, hpBmono, hpBcard, hBzero⟩ :=
    real_quasi_schur_blocks (Matrix.of B)
  let U : RMatFn m m := fun i j => Umat i j
  let V : RMatFn n n := fun i j => Vmat i j
  let R : RMatFn m m := rectMatMul (matTranspose U) (rectMatMul A U)
  let S : RMatFn n n := rectMatMul (matTranspose V) (rectMatMul B V)
  have hU : IsOrthogonal m U :=
    IsOrthogonal.of_mem_orthogonalGroup Umat hUmat
  have hV : IsOrthogonal n V :=
    IsOrthogonal.of_mem_orthogonalGroup Vmat hVmat
  have hA : A = rectMatMul U (rectMatMul R (matTranspose U)) :=
    (rectMatMul_schur_coords_expand U U A hU hU).symm
  have hB : B = rectMatMul V (rectMatMul S (matTranspose V)) :=
    (rectMatMul_schur_coords_expand V V B hV hV).symm
  have hRzero : ∀ i j : Fin m, pA j < pA i -> R i j = 0 := by
    intro i j hij
    have hleft :
        rectMatMul (rectMatMul (matTranspose U) A) U i j = 0 := by
      simpa [U, rectMatMul, matTranspose, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply] using hAzero i j hij
    have hassoc := rectMatMul_assoc (matTranspose U) A U
    have hentry := congrFun (congrFun hassoc i) j
    change (rectMatMul (matTranspose U) (rectMatMul A U)) i j = 0
    rw [← hentry]
    exact hleft
  have hSzero : ∀ i j : Fin n, pB j < pB i -> S i j = 0 := by
    intro i j hij
    have hleft :
        rectMatMul (rectMatMul (matTranspose V) B) V i j = 0 := by
      simpa [V, rectMatMul, matTranspose, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply] using hBzero i j hij
    have hassoc := rectMatMul_assoc (matTranspose V) B V
    have hentry := congrFun (congrFun hassoc i) j
    change (rectMatMul (matTranspose V) (rectMatMul B V)) i j = 0
    rw [← hentry]
    exact hleft
  refine ⟨U, R, V, S, pA, pB, hU, hV, hA, hB,
    hpAmono, hpAcard, hRzero, hpBmono, hpBcard, hSzero, ?_⟩
  exact sylvester_schur_transform_solution_iff m n U R A V S B C Y hU hV hA hB

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), source-numbered alias:
    real quasi-Schur factors for both sides of the Sylvester equation, with
    block maps of size at most two.  This is only the factor-existence surface,
    not the block solve or floating-point stability theorem. -/
theorem H16_eq16_4_sylvester_realQuasiSchur_factors (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    ∃ (U R : Matrix (Fin m) (Fin m) Real)
      (V S : Matrix (Fin n) (Fin n) Real)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      U ∈ Matrix.orthogonalGroup (Fin m) Real ∧
      V ∈ Matrix.orthogonalGroup (Fin n) Real ∧
      Matrix.transpose U * Matrix.of A * U = R ∧
      Matrix.transpose V * Matrix.of B * V = S ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) :=
  sylvester_realQuasiSchur_factors m n A B

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.5),
    source-numbered alias: choose real quasi-Schur coordinates and expose the
    exact equivalence between the original Sylvester equation and the
    transformed Schur-coordinate equation.  The subsequent block recurrence
    and floating-point analysis remain separate certificate surfaces. -/
theorem H16_eq16_4_5_sylvester_realQuasiSchur_transform_solution_iff
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Y : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      (IsSylvesterSolutionRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V))) ↔
        IsSylvesterSolutionRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) :=
  sylvester_realQuasiSchur_transform_solution_iff m n A B C Y

-- ============================================================
-- (16.3): constructive spectral directions
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), forward direction:
    a real eigenpair `A v = lam v` and a real eigenpair `B^T w = mu w`
    (equivalently: `w` is a left eigenvector of `B`; `B^T` has exactly the
    eigenvalues of `B`, which is Higham's `mu_j(B)`) produce the eigen-identity
    `(I_n kron A - B^T kron I_m) (w kron v) = (lam - mu) (w kron v)`.
    The Kronecker product vector `w kron v` is expressed as
    `Matrix.vec (v w^T)`, in exactly the column-stacking product-index
    convention of `sylvesterVecCoeff` and `sylvesterVecCoeff_mulVec_vec`:
    the entry at product index `p = (j, i)` is `v i * w j`.
    Nonvanishing of the eigenvector is `vec_outer_product_ne_zero` below.
    Scope: real eigenpairs only; the converse spectral inclusion needs a
    complex Schur form and is not formalized. -/
theorem sylvesterVecCoeff_eigenpair (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real)
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.mulVec (Matrix.transpose B) w = fun j => mu * w j) :
    Matrix.mulVec (sylvesterVecCoeff m n A B)
        (Matrix.vec (fun i j => v i * w j : RMatFn m n)) =
      fun p => (lam - mu) * (v p.2 * w p.1) := by
  rw [sylvesterVecCoeff_mulVec_vec]
  funext p
  have hvi : (Finset.sum Finset.univ fun l : Fin m => A p.2 l * v l) =
      lam * v p.2 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hv p.2
  have hwj : (Finset.sum Finset.univ fun l : Fin n => B l p.1 * w l) =
      mu * w p.1 := by
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using
      congrFun hw p.1
  show (Finset.sum Finset.univ fun l : Fin m => A p.2 l * (v l * w p.1)) -
      (Finset.sum Finset.univ fun l : Fin n => v p.2 * w l * B l p.1) =
    (lam - mu) * (v p.2 * w p.1)
  have h1 : (Finset.sum Finset.univ fun l : Fin m => A p.2 l * (v l * w p.1)) =
      (Finset.sum Finset.univ fun l : Fin m => A p.2 l * v l) * w p.1 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have h2 : (Finset.sum Finset.univ fun l : Fin n => v p.2 * w l * B l p.1) =
      v p.2 * (Finset.sum Finset.univ fun l : Fin n => B l p.1 * w l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1, h2, hvi, hwj]
  ring

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), forward direction, left
    eigenvector form: the same eigen-identity with the `B`-side eigenpair
    supplied as a left eigenpair `w^T B = mu w^T` of `B` itself, matching
    Higham's phrasing "the eigenvalues of `B`". -/
theorem sylvesterVecCoeff_eigenpair_vecMul (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real)
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.vecMul w B = fun j => mu * w j) :
    Matrix.mulVec (sylvesterVecCoeff m n A B)
        (Matrix.vec (fun i j => v i * w j : RMatFn m n)) =
      fun p => (lam - mu) * (v p.2 * w p.1) := by
  apply sylvesterVecCoeff_eigenpair m n A B v w lam mu hv
  funext j
  have hj : (Finset.sum Finset.univ fun l : Fin n => w l * B l j) =
      mu * w j := by
    simpa [Matrix.vecMul, dotProduct] using congrFun hw j
  have hmv : Matrix.mulVec (Matrix.transpose B) w j =
      Finset.sum Finset.univ fun l : Fin n => B l j * w l := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [hmv, ← hj]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3):
    the Kronecker product of two nonzero vectors, stacked as
    `Matrix.vec (v w^T)` in the module's column-stacking convention, is a
    nonzero product-index vector: pick indices where both factors are
    nonzero. -/
theorem vec_outer_product_ne_zero (m n : Nat)
    (v : Fin m -> Real) (w : Fin n -> Real)
    (hv : Not (v = 0)) (hw : Not (w = 0)) :
    Not (Matrix.vec (fun i j => v i * w j : RMatFn m n) = 0) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  intro h
  have hp := congrFun h (j, i)
  have hval : v i * w j = 0 := by
    simpa [Matrix.vec] using hp
  rcases mul_eq_zero.mp hval with h0 | h0
  · exact hi (by simpa using h0)
  · exact hj (by simpa using h0)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), forward direction in
    determinant form: for supplied nonzero real eigenpairs of `A` and `B^T`,
    the difference `lam - mu` is an eigenvalue of the vec/Kronecker Sylvester
    coefficient, witnessed by the vanishing of the shifted determinant
    `det(I_n kron A - B^T kron I_m - (lam - mu) I) = 0`.
    Scope: this is only the inclusion "every supplied real eigenpair
    difference is an eigenvalue"; the reverse inclusion needs a complex Schur
    form and is not formalized. -/
theorem sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.mulVec (Matrix.transpose B) w = fun j => mu * w j) :
    Matrix.det
        (sylvesterVecCoeff m n A B -
          (lam - mu) •
            (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
      0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sylvesterVecCoeff_eigenpair m n A B v w lam mu hv hw]
  funext p
  simp [Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), shifted determinant form
    with the `B`-side eigenpair supplied as a left eigenpair `w^T B = mu w^T`.
    The supplied real eigenpair difference `lam - mu` makes the shifted
    vec/Kronecker Sylvester coefficient singular. -/
theorem sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair_vecMul (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.vecMul w B = fun j => mu * w j) :
    Matrix.det
        (sylvesterVecCoeff m n A B -
          (lam - mu) •
            (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
      0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sylvesterVecCoeff_eigenpair_vecMul m n A B v w lam mu hv hw]
  funext p
  simp [Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), shifted nonsingular
    exclusion: if the shifted vec/Kronecker Sylvester coefficient at
    `lam - mu` has nonzero determinant, then no supplied nonzero real
    eigenpairs of `A` and `B^T` can have those eigenvalues. -/
theorem no_real_eigenpair_difference_of_sylvesterVecCoeff_shifted_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (lam mu : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff m n A B -
          (lam - mu) •
            (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
        0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.mulVec (Matrix.transpose B) w = (fun j => mu * w j)) := by
  rintro ⟨v, w, hv0, hw0, hv, hw⟩
  exact hdet
    (sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair
      m n A B v w lam mu hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-facing shifted
    nonsingular exclusion with the `B` eigenpair supplied in left-eigenvector
    form. -/
theorem no_real_left_eigenpair_difference_of_sylvesterVecCoeff_shifted_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (lam mu : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff m n A B -
          (lam - mu) •
            (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
        0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.vecMul w B = (fun j => mu * w j)) := by
  rintro ⟨v, w, hv0, hw0, hv, hw⟩
  exact hdet
    (sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair_vecMul
      m n A B v w lam mu hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3) and the common-eigenvalue
    criterion, constructive direction: a shared real eigenvalue of `A` and
    `B^T` (equivalently of `B`) yields the nonzero kernel vector
    `vec(v w^T)`, so the vec/Kronecker Sylvester coefficient is singular.
    This generalizes the diagonal case
    `sylvesterVecCoeff_diagonal_det_eq_zero_of_common_entry` of
    `Higham16.lean` to arbitrary supplied eigenpairs.
    Scope: the converse (no common eigenvalue implies nonsingularity) needs
    simultaneous triangularization over the complex numbers and remains
    open. -/
theorem sylvesterVecCoeff_singular_of_common_eigenvalue (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.mulVec (Matrix.transpose B) w = fun j => lam * w j) :
    Matrix.det (sylvesterVecCoeff m n A B) = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [sylvesterVecCoeff_eigenpair m n A B v w lam lam hv hw]
  funext p
  simp

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), left-eigenvector form:
    a shared supplied real eigenvalue of `A` and `B`, with the `B` side given
    as a left eigenpair `w^T B = lam w^T`, makes the vec/Kronecker Sylvester
    coefficient singular.  This is the constructive common-eigenvalue
    obstruction, not the full converse spectral theorem. -/
theorem sylvesterVecCoeff_singular_of_common_left_eigenvalue (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.vecMul w B = fun j => lam * w j) :
    Matrix.det (sylvesterVecCoeff m n A B) = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [sylvesterVecCoeff_eigenpair_vecMul m n A B v w lam lam hv hw]
  funext p
  simp

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), nonsingular exclusion:
    if the vec/Kronecker Sylvester coefficient has nonzero determinant, then
    there is no supplied nonzero real eigenpair of `A` and `B^T` with the same
    eigenvalue.  This is the contrapositive of the constructive
    common-eigenvalue obstruction and does not prove the full complex spectral
    converse. -/
theorem no_common_real_eigenpair_of_sylvesterVecCoeff_det_ne_zero (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.mulVec (Matrix.transpose B) w = (fun j => lam * w j)) := by
  rintro ⟨v, w, lam, hv0, hw0, hv, hw⟩
  exact hdet
    (sylvesterVecCoeff_singular_of_common_eigenvalue
      m n A B v w lam hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), nonsingular exclusion in
    the source-facing left-eigenvector form: a nonzero determinant for the
    vec/Kronecker Sylvester coefficient rules out supplied nonzero real
    eigenpairs `A v = lam v` and `w^T B = lam w^T`. -/
theorem no_common_real_left_eigenpair_of_sylvesterVecCoeff_det_ne_zero
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.vecMul w B = (fun j => lam * w j)) := by
  rintro ⟨v, w, lam, hv0, hw0, hv, hw⟩
  exact hdet
    (sylvesterVecCoeff_singular_of_common_left_eigenvalue
      m n A B v w lam hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias:
    supplied real eigenpairs `A v = lam v` and `w^T B = mu w^T` give the
    forward vec/Kronecker eigen-identity with eigenvalue difference
    `lam - mu`.  This is the constructive real left-eigenpair direction only;
    it does not assert the full complex spectral converse. -/
theorem H16_eq16_3_sylvesterVecCoeff_eigenpair_vecMul :
    forall (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
      (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real),
      Matrix.mulVec A v = (fun i => lam * v i) ->
      Matrix.vecMul w B = (fun j => mu * w j) ->
      Matrix.mulVec (sylvesterVecCoeff m n A B)
          (Matrix.vec (fun i j => v i * w j : RMatFn m n)) =
        fun p => (lam - mu) * (v p.2 * w p.1) :=
  fun m n A B v w lam mu hv hw =>
    sylvesterVecCoeff_eigenpair_vecMul m n A B v w lam mu hv hw

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias:
    for supplied nonzero real eigenpairs of `A` and a left eigenpair of `B`,
    the shifted vec/Kronecker Sylvester coefficient at `lam - mu` is singular.
    This proves the real constructive inclusion, not the reverse spectral
    characterization. -/
theorem H16_eq16_3_sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair_vecMul :
    forall (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
      (v : Fin m -> Real) (w : Fin n -> Real) (lam mu : Real),
      Not (v = 0) -> Not (w = 0) ->
      Matrix.mulVec A v = (fun i => lam * v i) ->
      Matrix.vecMul w B = (fun j => mu * w j) ->
      Matrix.det
          (sylvesterVecCoeff m n A B -
            (lam - mu) •
              (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
        0 :=
  fun m n A B v w lam mu hv0 hw0 hv hw =>
    sylvesterVecCoeff_shifted_det_eq_zero_of_eigenpair_vecMul
      m n A B v w lam mu hv0 hw0 hv hw

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias:
    a supplied common real eigenvalue of `A` and `B`, with the `B` eigenpair in
    left-eigenvector form, makes the vectorized Sylvester coefficient singular.
    This is the constructive obstruction direction only. -/
theorem H16_eq16_3_sylvesterVecCoeff_singular_of_common_left_eigenvalue :
    forall (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
      (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) -> Not (w = 0) ->
      Matrix.mulVec A v = (fun i => lam * v i) ->
      Matrix.vecMul w B = (fun j => lam * w j) ->
      Matrix.det (sylvesterVecCoeff m n A B) = 0 :=
  fun m n A B v w lam hv0 hw0 hv hw =>
    sylvesterVecCoeff_singular_of_common_left_eigenvalue
      m n A B v w lam hv0 hw0 hv hw

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias:
    nonzero determinant of the shifted vec/Kronecker coefficient rules out
    supplied nonzero real left-eigenpair data with eigenvalue difference
    `lam - mu`. -/
theorem H16_eq16_3_no_real_left_eigenpair_difference_of_shifted_det_ne_zero :
    forall (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (lam mu : Real),
      Not (Matrix.det
        (sylvesterVecCoeff m n A B -
          (lam - mu) •
            (1 : Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)) =
        0) ->
      Not (exists (v : Fin m -> Real) (w : Fin n -> Real),
        Not (v = 0) /\ Not (w = 0) /\
          Matrix.mulVec A v = (fun i => lam * v i) /\
          Matrix.vecMul w B = (fun j => mu * w j)) :=
  fun m n A B lam mu hdet =>
    no_real_left_eigenpair_difference_of_sylvesterVecCoeff_shifted_det_ne_zero
      m n A B lam mu hdet

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias:
    determinant nonsingularity of the vec/Kronecker Sylvester coefficient rules
    out supplied common real eigenpairs in source-facing left-eigenvector form.
    This does not prove the full complex no-common-spectrum converse. -/
theorem H16_eq16_3_no_common_real_left_eigenpair_of_det_ne_zero :
    forall (m n : Nat) (A : RMatFn m m) (B : RMatFn n n),
      Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) ->
      Not (exists (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
        Not (v = 0) /\ Not (w = 0) /\
          Matrix.mulVec A v = (fun i => lam * v i) /\
          Matrix.vecMul w B = (fun j => lam * w j)) :=
  fun m n A B hdet =>
    no_common_real_left_eigenpair_of_sylvesterVecCoeff_det_ne_zero
      m n A B hdet

-- ============================================================
-- (16.4)-(16.8): Bartels-Stewart supplied-triangular column solve
-- ============================================================

/-- Upper triangularity for the function-shaped square matrices used by the
    Chapter 16 rectangular Sylvester surfaces: all entries strictly below the
    diagonal vanish.  This is the supplied-factor structure of the
    Bartels-Stewart matrix `S` in Higham, 2nd ed., Chapter 16.2, equations
    (16.4)-(16.5); it agrees with Mathlib's `Matrix.BlockTriangular T id`. -/
def IsUpperTriangularFn (n : Nat) (T : RMatFn n n) : Prop :=
  forall i j : Fin n, j < i -> T i j = 0

/-- A real quasi-Schur zero pattern becomes an ordinary upper-triangular
    pattern when the supplied block map has no repeated adjacent block labels.
    This is only a structural adapter; it does not assert that real Schur
    factors are triangular in general. -/
theorem IsUpperTriangularFn.of_quasiSchur_strictBlockMap (n : Nat)
    (T : RMatFn n n) (p : Fin n -> Nat)
    (hzero : ∀ i j : Fin n, p j < p i -> T i j = 0)
    (hp : ∀ i j : Fin n, j < i -> p j < p i) :
    IsUpperTriangularFn n T := by
  intro i j hij
  exact hzero i j (hp i j hij)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    the shifted column coefficient `A - t I` appearing in the
    Bartels-Stewart column solve `(A - t_kk I) x_k = ...`. -/
noncomputable def sylvesterTriangularShiftedCoeff (m : Nat)
    (A : RMatFn m m) (t : Real) : Matrix (Fin m) (Fin m) Real :=
  Matrix.of A - t • (1 : Matrix (Fin m) (Fin m) Real)

/-- Entrywise action of the shifted column coefficient:
    `((A - t I) x)_i = (sum_l a_il x_l) - t x_i`. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_apply (m : Nat)
    (A : RMatFn m m) (t : Real) (x : Fin m -> Real) (i : Fin m) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t) x i =
      (Finset.sum Finset.univ fun l : Fin m => A i l * x l) - t * x i := by
  unfold sylvesterTriangularShiftedCoeff
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.of_apply]

private theorem triangular_column_sum_split (m n : Nat) (T : RMatFn n n)
    (hT : IsUpperTriangularFn n T) (X : RMatFn m n) (i : Fin m) (k : Fin n) :
    (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) =
      T k k * X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  have hsub : Finset.sum (Finset.filter (fun j => j <= k) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum Finset.univ fun j : Fin n => X i j * T j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjnot
    have hnot : Not (j <= k) := by
      intro hle
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
    have hkj : k < j := not_le.mp hnot
    rw [hT j k hkj, mul_zero]
  rw [← hsub]
  have hset : Finset.filter (fun j => j <= k) Finset.univ =
      insert k (Finset.filter (fun j => j < k) Finset.univ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl heq
    · intro h
      rcases h with heq | hlt
      · exact le_of_eq heq
      · exact le_of_lt hlt
  have hknotmem : k ∉ Finset.filter (fun j => j < k) Finset.univ := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl k)
  rw [hset, Finset.sum_insert hknotmem, mul_comm (X i k) (T k k)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Supplied adjacent `2 x 2` diagonal block shape for the function-shaped
    quasi-upper-triangular factors used in the real Bartels-Stewart route:
    columns `p` and `q` are adjacent, and entries below row `q` vanish in
    those two columns.  The in-block subdiagonal entry `T q p` may be nonzero. -/
def IsAdjacentQuasiTriangularBlockFn (n : Nat) (T : RMatFn n n)
    (p q : Fin n) : Prop :=
  q.val = p.val + 1 ∧
    (∀ j : Fin n, q < j → T j p = 0) ∧
    (∀ j : Fin n, q < j → T j q = 0)

/-- A size-at-most-two real quasi-Schur block map is strict after an adjacent
    same-block pair.  This is the small order-theoretic adapter needed to turn
    the exported block-map zeros of `real_quasi_schur_blocks` into the supplied
    adjacent two-column zero pattern used by the real Bartels-Stewart block
    recurrence. -/
theorem quasiSchur_blockMap_strict_after_adjacent_same_block (n : Nat)
    (pmap : Fin n -> Nat) (p q j : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hqj : q < j) :
    pmap q < pmap j := by
  have hle : pmap q <= pmap j := hmono (le_of_lt hqj)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hp_ne_q : p ≠ q := ne_of_lt hpq_lt
  have hp_ne_j : p ≠ j := ne_of_lt (lt_trans hpq_lt hqj)
  have hq_ne_j : q ≠ j := ne_of_lt hqj
  let fiber : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => pmap i = pmap q)
  have hsubset : ({p, q, j} : Finset (Fin n)) ⊆ fiber := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x
      simp [fiber, hsame]
    · subst x
      simp [fiber]
    · subst x
      simp [fiber, heq.symm]
  have hthree : 3 <= fiber.card := by
    have hcard_three : ({p, q, j} : Finset (Fin n)).card = 3 := by
      simp [hp_ne_q, hp_ne_j, hq_ne_j]
    calc
      3 = ({p, q, j} : Finset (Fin n)).card := hcard_three.symm
      _ <= fiber.card := Finset.card_le_card hsubset
  have htwo : fiber.card <= 2 := hcard (pmap q)
  omega

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): a same-labelled
    adjacent two-column block in the exported real quasi-Schur block map gives
    the supplied adjacent quasi-triangular block predicate used by the exact
    two-column Bartels-Stewart recurrence.  The theorem supplies only the zero
    pattern; nonsingularity of the induced `2 x 2` block coefficient remains a
    separate spectral/block-separation certificate. -/
theorem IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block (n : Nat)
    (T : RMatFn n n) (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q) :
    IsAdjacentQuasiTriangularBlockFn n T p q := by
  refine ⟨hpq, ?_, ?_⟩
  · intro j hqj
    apply hzero j p
    rw [hsame]
    exact quasiSchur_blockMap_strict_after_adjacent_same_block
      n pmap p q j hmono hcard hpq hsame hqj
  · intro j hqj
    apply hzero j q
    exact quasiSchur_blockMap_strict_after_adjacent_same_block
      n pmap p q j hmono hcard hpq hsame hqj

private theorem two_column_block_sum_split (m n : Nat) (T : RMatFn n n)
    (X : RMatFn m n) (i : Fin m) (p q k : Fin n)
    (hpq : q.val = p.val + 1)
    (hbelow : ∀ j : Fin n, q < j → T j k = 0) :
    (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) =
      T p k * X i p + T q k * X i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j k * X i j) := by
  have hpq_lt : p < q := Fin.lt_def.mpr (by omega)
  have hsub : Finset.sum (Finset.filter (fun j => j <= q) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum Finset.univ fun j : Fin n => X i j * T j k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hjnot
    have hnot : Not (j <= q) := by
      intro hle
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
    have hqj : q < j := not_le.mp hnot
    rw [hbelow j hqj, mul_zero]
  rw [← hsub]
  have hset : Finset.filter (fun j => j <= q) Finset.univ =
      insert q (insert p (Finset.filter (fun j => j < p) Finset.univ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hjle
      by_cases hjq : j = q
      · exact Or.inl hjq
      · right
        by_cases hjp : j = p
        · exact Or.inl hjp
        · right
          apply Fin.lt_def.mpr
          have hjleNat : j.val <= q.val := Fin.le_def.mp hjle
          have hjqNat : j.val ≠ q.val := by
            intro hval
            exact hjq (Fin.ext hval)
          have hjpNat : j.val ≠ p.val := by
            intro hval
            exact hjp (Fin.ext hval)
          omega
    · intro h
      rcases h with heq | heq | hlt
      · exact le_of_eq heq
      · rw [heq]
        exact le_of_lt hpq_lt
      · exact le_trans (le_of_lt hlt) (le_of_lt hpq_lt)
  have hpnotmem : p ∉ Finset.filter (fun j => j < p) Finset.univ := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl p)
  have hqnotmem :
      q ∉ insert p (Finset.filter (fun j => j < p) Finset.univ) := by
    intro hmem
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases hmem with hqp | hqprev
    · exact (ne_of_gt hpq_lt) hqp
    · exact (not_lt_of_ge (le_of_lt hpq_lt)) hqprev
  rw [hset, Finset.sum_insert hqnotmem, Finset.sum_insert hpnotmem]
  have hprev : Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => X i j * T j k) =
      Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
        (fun j => T j k * X i j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprev]
  ring

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    adjacent `2 x 2` quasi-triangular block system: the two active columns
    are kept on the left-hand side, while only previously solved columns
    `j < p` appear in the right-hand side. -/
def IsSylvesterTwoColumnBlockSystem (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) : Prop :=
  (fun i =>
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p))
          (fun i' => X i' p) i - T q p * X i q) =
    (fun i =>
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j)) ∧
  (fun i =>
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q))
          (fun i' => X i' q) i - T p q * X i p) =
    (fun i =>
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), supplied adjacent
    `2 x 2` block coefficient for the two active block columns in the real
    Bartels-Stewart recurrence.  The diagonal blocks are the shifted column
    coefficients, and the off-diagonal blocks are the scalar couplings inside
    the supplied quasi-triangular diagonal block.  Scope: exact supplied-block
    algebra only; no Schur existence, block nonsingularity, or floating-point
    error propagation from (16.7)-(16.8) is asserted. -/
noncomputable def sylvesterTwoColumnBlockCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks
    (sylvesterTriangularShiftedCoeff m A (T p p))
    ((- (T q p)) • (1 : Matrix (Fin m) (Fin m) Real))
    ((- (T p q)) • (1 : Matrix (Fin m) (Fin m) Real))
    (sylvesterTriangularShiftedCoeff m A (T q q))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), first-column
    quadratic coefficient induced by the supplied adjacent two-column block.
    A zero vector for the full block coefficient forces the first active
    column through this product-shift coefficient. -/
noncomputable def sylvesterTwoColumnBlockFirstQuadraticCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Fin m) (Fin m) Real :=
  sylvesterTriangularShiftedCoeff m A (T q q) *
      sylvesterTriangularShiftedCoeff m A (T p p) -
    Matrix.scalar (Fin m) (T q p * T p q)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), second-column
    quadratic coefficient induced by the supplied adjacent two-column block.
    This is the companion product-shift condition for the second active
    column. -/
noncomputable def sylvesterTwoColumnBlockSecondQuadraticCoeff (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix (Fin m) (Fin m) Real :=
  sylvesterTriangularShiftedCoeff m A (T p p) *
      sylvesterTriangularShiftedCoeff m A (T q q) -
    Matrix.scalar (Fin m) (T p q * T q p)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    kernel reduction for the supplied adjacent two-column block: a vector in
    the kernel of the `2 x 2` block coefficient has first and second active
    components in the kernels of the two product-shift quadratic coefficients.
    This is exact block algebra and does not use a supplied inverse. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_quadratic (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (z : Sum (Fin m) (Fin m) -> Real)
    (hz : Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0) :
    Matrix.mulVec (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q)
        (fun i : Fin m => z (Sum.inl i)) = 0 /\
      Matrix.mulVec (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q)
        (fun i : Fin m => z (Sum.inr i)) = 0 := by
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  have hP : Matrix.mulVec P u = fun i : Fin m => T q p * v i := by
    funext i
    have hi := congrFun hz (Sum.inl i)
    have hi' : Matrix.mulVec P u i + (-(T q p)) * v i = 0 := by
      simpa [sylvesterTwoColumnBlockCoeff, P, Q, u, v,
        Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hi
    linarith
  have hQ : Matrix.mulVec Q v = fun i : Fin m => T p q * u i := by
    funext i
    have hi := congrFun hz (Sum.inr i)
    have hi' : Matrix.mulVec Q v i + (-(T p q)) * u i = 0 := by
      simpa [sylvesterTwoColumnBlockCoeff, P, Q, u, v,
        Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        add_comm, add_left_comm, add_assoc] using hi
    linarith
  constructor
  case left =>
    funext i
    have hsmul : Matrix.mulVec Q (fun i : Fin m => T q p * v i) =
        fun i : Fin m => T q p * Matrix.mulVec Q v i := by
      simpa using Matrix.mulVec_smul Q (T q p) v
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) u i =
          Matrix.mulVec Q (Matrix.mulVec P u) i - (T q p * T p q) * u i := by
        simp [sylvesterTwoColumnBlockFirstQuadraticCoeff, P, Q, Matrix.sub_mulVec,
          Matrix.mulVec_mulVec, Matrix.scalar_apply]
      _ = Matrix.mulVec Q (fun i : Fin m => T q p * v i) i -
            (T q p * T p q) * u i := by rw [hP]
      _ = T q p * Matrix.mulVec Q v i - (T q p * T p q) * u i := by rw [hsmul]
      _ = T q p * (T p q * u i) - (T q p * T p q) * u i := by rw [hQ]
      _ = 0 := by ring
  case right =>
    funext i
    have hsmul : Matrix.mulVec P (fun i : Fin m => T p q * u i) =
        fun i : Fin m => T p q * Matrix.mulVec P u i := by
      simpa using Matrix.mulVec_smul P (T p q) u
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) v i =
          Matrix.mulVec P (Matrix.mulVec Q v) i - (T p q * T q p) * v i := by
        simp [sylvesterTwoColumnBlockSecondQuadraticCoeff, P, Q, Matrix.sub_mulVec,
          Matrix.mulVec_mulVec, Matrix.scalar_apply]
      _ = Matrix.mulVec P (fun i : Fin m => T p q * u i) i -
            (T p q * T q p) * v i := by rw [hQ]
      _ = T p q * Matrix.mulVec P u i - (T p q * T q p) * v i := by rw [hsmul]
      _ = T p q * (T q p * v i) - (T p q * T q p) * v i := by rw [hP]
      _ = 0 := by ring

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    bridge for the supplied adjacent two-column block: nonsingularity of the
    two induced product-shift quadratic coefficients rules out a kernel vector
    of the full `2 x 2` block coefficient. This removes the need for a
    supplied left/right inverse certificate at this local block step; the
    remaining source-level route is to derive these quadratic determinant
    hypotheses from the real-Schur scalar block separation data. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hfirst :
      Not (Matrix.det
        (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) = 0))
    (hsecond :
      Not (Matrix.det
        (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  cases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with
  | intro z hz =>
      have hzne : Not (z = 0) := hz.1
      have hzzero :
          Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 := hz.2
      have hquad :=
        sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_quadratic
          m n A T p q z hzzero
      let u : Fin m -> Real := fun i => z (Sum.inl i)
      let v : Fin m -> Real := fun i => z (Sum.inr i)
      let M1 : Matrix (Fin m) (Fin m) Real :=
        sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q
      let M2 : Matrix (Fin m) (Fin m) Real :=
        sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q
      have hinj1 : Function.Injective (Matrix.mulVec M1) := by
        intro x y hxy
        have h := congrArg (Matrix.mulVec (Inv.inv M1)) hxy
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul M1
            (isUnit_iff_ne_zero.mpr (by simpa [M1] using hfirst)),
          Matrix.one_mulVec, Matrix.one_mulVec] at h
        exact h
      have hinj2 : Function.Injective (Matrix.mulVec M2) := by
        intro x y hxy
        have h := congrArg (Matrix.mulVec (Inv.inv M2)) hxy
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul M2
            (isUnit_iff_ne_zero.mpr (by simpa [M2] using hsecond)),
          Matrix.one_mulVec, Matrix.one_mulVec] at h
        exact h
      have hu : u = 0 := by
        apply hinj1
        rw [hquad.1, Matrix.mulVec_zero]
      have hv : v = 0 := by
        apply hinj2
        rw [hquad.2, Matrix.mulVec_zero]
      apply hzne
      funext r
      cases r with
      | inl i => simpa [u] using congrFun hu i
      | inr i => simpa [v] using congrFun hv i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    determinant symmetry for the supplied adjacent two-column block: the two
    quadratic coefficients have the same determinant.  This is exact algebra
    (`det (Q * P - c I) = det (P * Q - c I)`) and reduces the structural
    block nonsingularity route to a single product-shift determinant
    certificate. -/
theorem sylvesterTwoColumnBlockFirstQuadraticCoeff_det_eq_secondQuadraticCoeff_det
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) :
    Matrix.det (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) =
      Matrix.det (sylvesterTwoColumnBlockSecondQuadraticCoeff m n A T p q) := by
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let c : Real := T q p * T p q
  have hchar := congrArg (fun f : Polynomial Real => f.eval c)
    (Matrix.charpoly_mul_comm Q P)
  change (Q * P).charpoly.eval c = (P * Q).charpoly.eval c at hchar
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly] at hchar
  have hleft : Matrix.scalar (Fin m) c - Q * P = -(Q * P - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  have hright : Matrix.scalar (Fin m) c - P * Q = -(P * Q - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  rw [hleft, hright, Matrix.det_neg, Matrix.det_neg] at hchar
  have hneg : Not ((-1 : Real) = 0) := by norm_num
  have hfactor : Not (((-1 : Real) ^ Fintype.card (Fin m)) = 0) :=
    pow_ne_zero (Fintype.card (Fin m)) hneg
  have hdet : Matrix.det (Q * P - Matrix.scalar (Fin m) c) =
      Matrix.det (P * Q - Matrix.scalar (Fin m) c) :=
    (mul_eq_mul_left_iff.mp hchar).resolve_right hfactor
  simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff,
    sylvesterTwoColumnBlockSecondQuadraticCoeff, P, Q, c, mul_comm] using hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    determinant bridge for a supplied adjacent two-column block: it is enough
    to prove nonsingularity of one product-shift quadratic coefficient.  The
    companion quadratic determinant condition follows from
    `det (Q * P - c I) = det (P * Q - c I)`, so this is the one-certificate
    block nonsingularity surface needed before deriving the product-shift
    condition from real-Schur spectral separation data. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_first_quadratic_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hfirst :
      Not (Matrix.det
        (sylvesterTwoColumnBlockFirstQuadraticCoeff m n A T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    m n A T p q hfirst
  intro hsecond
  exact hfirst
    ((sylvesterTwoColumnBlockFirstQuadraticCoeff_det_eq_secondQuadraticCoeff_det
      m n A T p q).trans hsecond)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    spectral certificate for a supplied adjacent two-column block: if the
    coupling product is not a root of the characteristic polynomial of the
    product of the two shifted column coefficients, then the full block
    coefficient is nonsingular.  This is the spectral-facing form of the
    one-quadratic determinant certificate. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_charpoly
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hchar :
      Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
          (T q p * T p q) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_first_quadratic_det_ne_zero
  intro hdet
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let c : Real := T q p * T p q
  have hdet' : Matrix.det (Q * P - Matrix.scalar (Fin m) c) = 0 := by
    simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff, P, Q, c] using hdet
  have hleft : Matrix.scalar (Fin m) c - Q * P =
      -(Q * P - Matrix.scalar (Fin m) c) := by
    simp [neg_sub]
  have hcharzero : (Q * P).charpoly.eval c = 0 := by
    rw [Matrix.eval_charpoly, hleft, Matrix.det_neg, hdet', mul_zero]
  exact hchar (by simpa [P, Q, c] using hcharzero)

/-- Finite-matrix spectral kernel bridge: if the only vector satisfying
    `M x = c x` is zero, then `c` is not a root of `M.charpoly`.  This is the
    reusable determinant-free surface used below to turn a product-shift
    no-eigenvector hypothesis into the Chapter 16 two-column block
    nonsingularity certificate. -/
theorem finiteMatrix_charpoly_eval_ne_zero_of_mulVec_no_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι Real) (c : Real)
    (hker : forall x : ι -> Real,
      Matrix.mulVec M x = (fun i => c * x i) -> x = 0) :
    Not (M.charpoly.eval c = 0) := by
  intro hchar
  have hdet : Matrix.det (Matrix.scalar ι c - M) = 0 := by
    simpa [Matrix.eval_charpoly] using hchar
  obtain ⟨x, hxne, hxzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hxM : Matrix.mulVec M x = fun i => c * x i := by
    funext i
    have hi := congrFun hxzero i
    have hi' : c * x i - Matrix.mulVec M x i = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi
    linarith
  exact hxne (hker x hxM)

/-- Finite-matrix nonroot kernel bridge: if `c` is not a root of
    `M.charpoly`, then the eigen-equation `M x = c x` has only the zero
    solution.  This is the source-shaped converse to
    `finiteMatrix_charpoly_eval_ne_zero_of_mulVec_no_eigenvector`. -/
theorem finiteMatrix_mulVec_no_eigenvector_of_charpoly_eval_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι Real) (c : Real)
    (hchar : Not (M.charpoly.eval c = 0)) :
    forall x : ι -> Real,
      Matrix.mulVec M x = (fun i => c * x i) -> x = 0 := by
  intro x hx
  by_contra hxne
  have hxzero : Matrix.mulVec (Matrix.scalar ι c - M) x = 0 := by
    funext i
    have hi := congrFun hx i
    have hi' : c * x i - Matrix.mulVec M x i = 0 := by
      rw [hi]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi'
  have hdet : Matrix.det (Matrix.scalar ι c - M) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hxne, hxzero⟩
  exact hchar (by simpa [Matrix.eval_charpoly] using hdet)

/-- Finite-matrix product-shift determinant kernel bridge: nonsingularity of
    `M - c I` rules out nonzero solutions of the eigen-equation `M x = c x`.
    This is a determinant-facing route to the no-eigenvector hypothesis used
    by the structural two-column block solve. -/
theorem finiteMatrix_mulVec_no_eigenvector_of_det_sub_scalar_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι Real) (c : Real)
    (hdet : Not (Matrix.det (M - Matrix.scalar ι c) = 0)) :
    forall x : ι -> Real,
      Matrix.mulVec M x = (fun i => c * x i) -> x = 0 := by
  intro x hx
  by_contra hxne
  have hxzero : Matrix.mulVec (M - Matrix.scalar ι c) x = 0 := by
    funext i
    have hi := congrFun hx i
    have hi' : Matrix.mulVec M x i - c * x i = 0 := by
      rw [hi]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi'
  have hsing : Matrix.det (M - Matrix.scalar ι c) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hxne, hxzero⟩
  exact hdet hsing

/-- Finite complex-matrix intertwiner bridge: if `A * X = X * B`, then the
    image under `X` of a supplied `B` eigenvector is an `A` eigenvector with
    the same eigenvalue.  This is the algebraic core needed to turn a
    nonzero two-column intertwiner into a shared complex eigenvalue in the
    Chapter 16 real-Schur block-separation route. -/
theorem finiteComplexMatrix_intertwiner_maps_mulVec_eigenvector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι Complex) (B : Matrix κ κ Complex)
    (X : Matrix ι κ Complex) (mu : Complex) (w : κ -> Complex)
    (hX : A * X = X * B)
    (hw : Matrix.mulVec B w = fun j => mu * w j) :
    Matrix.mulVec A (Matrix.mulVec X w) =
      fun i => mu * Matrix.mulVec X w i := by
  calc
    Matrix.mulVec A (Matrix.mulVec X w) = Matrix.mulVec (A * X) w := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (X * B) w := by rw [hX]
    _ = Matrix.mulVec X (Matrix.mulVec B w) := by
      rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec X (fun j => mu * w j) := by rw [hw]
    _ = fun i => mu * Matrix.mulVec X w i := by
      simpa using Matrix.mulVec_smul X mu w

/-- Finite complex-matrix intertwiner eigenpair bridge: if `A * X = X * B`
    and a supplied `B` eigenvector has nonzero image under `X`, then `A`
    has a supplied nonzero eigenvector with the same eigenvalue. -/
theorem finiteComplexMatrix_exists_mulVec_eigenpair_of_intertwiner_image_ne_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι Complex) (B : Matrix κ κ Complex)
    (X : Matrix ι κ Complex) (mu : Complex) (w : κ -> Complex)
    (hX : A * X = X * B)
    (hw : Matrix.mulVec B w = fun j => mu * w j)
    (hXw : Matrix.mulVec X w ≠ 0) :
    ∃ y : ι -> Complex,
      y ≠ 0 ∧ Matrix.mulVec A y = fun i => mu * y i :=
  ⟨Matrix.mulVec X w, hXw,
    finiteComplexMatrix_intertwiner_maps_mulVec_eigenvector
      A B X mu w hX hw⟩

/-- A nonzero shifted determinant rules out a supplied complex eigenpair. -/
theorem finiteComplexMatrix_no_eigenpair_of_det_sub_scalar_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Complex) (mu : Complex)
    (hdet : Not (Matrix.det (A - Matrix.scalar ι mu) = 0)) :
    ¬ ∃ y : ι -> Complex,
      y ≠ 0 ∧ Matrix.mulVec A y = fun i => mu * y i := by
  intro hEig
  rcases hEig with ⟨y, hyne, hy⟩
  have hyzero : Matrix.mulVec (A - Matrix.scalar ι mu) y = 0 := by
    funext i
    have hi := congrFun hy i
    have hcoord : Matrix.mulVec A y i - mu * y i = 0 := by
      rw [hi]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hcoord
  have hsing : Matrix.det (A - Matrix.scalar ι mu) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hyne, hyzero⟩
  exact hdet hsing

/-- A finite complex matrix with no supplied eigenpair at `mu` has nonzero
    shifted determinant.  This is the converse direction used to turn a
    source-level no-common-complex-eigenvalue hypothesis into the determinant
    certificate required by the real-Schur two-column block route. -/
theorem finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_eigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Complex) (mu : Complex)
    (hno :
      ¬ ∃ y : ι -> Complex,
        y ≠ 0 ∧ Matrix.mulVec A y = fun i => mu * y i) :
    Not (Matrix.det (A - Matrix.scalar ι mu) = 0) := by
  intro hdet
  rcases (Matrix.exists_mulVec_eq_zero_iff.mpr hdet) with ⟨y, hyne, hyzero⟩
  exact hno ⟨y, hyne, by
    funext i
    have hi := congrFun hyzero i
    have hcoord : Matrix.mulVec A y i - mu * y i = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hi
    exact sub_eq_zero.mp hcoord⟩

/-- A source-facing right-eigenvalue predicate over complex matrices: `mu` is
    realized by a supplied nonzero right eigenvector of `A`. -/
def HasComplexRightEigenvalue {ι : Type*} [Fintype ι]
    (A : Matrix ι ι Complex) (mu : Complex) : Prop :=
  ∃ y : ι -> Complex,
    y ≠ 0 ∧ Matrix.mulVec A y = fun i => mu * y i

/-- Source-facing no-common-complex-right-eigenvalue predicate for two complex
    matrices, matching Higham's spectral-separation condition for the exact
    Sylvester equation. -/
def NoCommonComplexRightEigenvalue {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι Complex) (B : Matrix κ κ Complex) : Prop :=
  ∀ mu : Complex, ¬ (HasComplexRightEigenvalue A mu ∧
    HasComplexRightEigenvalue B mu)

/-- A left-oriented no-common-eigenvalue hypothesis plus a supplied right
    eigenvalue of `B` gives the shifted determinant separation for `A`.  This
    is a small orientation adapter used by the real-Schur two-column route. -/
theorem finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_common_right_eigenvalue_left
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι ι Complex) (B : Matrix κ κ Complex) (mu : Complex)
    (hno : NoCommonComplexRightEigenvalue A B)
    (hB : HasComplexRightEigenvalue B mu) :
    Not (Matrix.det (A - Matrix.scalar ι mu) = 0) := by
  exact finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_eigenpair A mu
    (fun hA => hno mu ⟨hA, hB⟩)

/-- Entrywise real-to-complex map for rectangular matrices.  This is the
    rectangular companion to the square complexification used in the real
    invariant-subspace development. -/
def realMatrixToComplex {ι κ : Type*}
    (M : Matrix ι κ Real) : Matrix ι κ Complex :=
  M.map Complex.ofRealHom

@[simp] theorem realMatrixToComplex_apply {ι κ : Type*}
    (M : Matrix ι κ Real) (i : ι) (j : κ) :
    realMatrixToComplex M i j = (M i j : Complex) := rfl

/-- Real-to-complex matrix conversion preserves finite matrix multiplication. -/
theorem realMatrixToComplex_mul {ι κ τ : Type*} [Fintype κ]
    (A : Matrix ι κ Real) (B : Matrix κ τ Real) :
    realMatrixToComplex (A * B) =
      realMatrixToComplex A * realMatrixToComplex B := by
  simp [realMatrixToComplex]

/-- Entrywise complexification sends the real Sylvester vec/Kronecker
    coefficient `I_n kron A - B^T kron I_m` to its complex counterpart. -/
theorem realMatrixToComplex_sylvesterVecCoeff (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    realMatrixToComplex (sylvesterVecCoeff m n A B) =
      complexSylvesterVecCoeff (realMatrixToComplex A) (realMatrixToComplex B) := by
  ext p q
  by_cases hp : p.1 = q.1 <;> by_cases hq : p.2 = q.2 <;>
    simp [realMatrixToComplex, sylvesterVecCoeff, complexSylvesterVecCoeff,
      Matrix.kronecker, Matrix.transpose_apply, Matrix.one_apply, hp, hq]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), complex spectral
    nonsingularity route for the real vec/Kronecker coefficient: if the
    entrywise complexifications of the real matrices `A` and `B` have no
    common supplied complex right eigenpair, then the real coefficient
    `I_n kron A - B^T kron I_m` has nonzero determinant. -/
theorem sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 := by
  intro hdet
  have hmap :
      Matrix.det (realMatrixToComplex (sylvesterVecCoeff m n A B)) =
        Complex.ofRealHom (Matrix.det (sylvesterVecCoeff m n A B)) := by
    simpa [realMatrixToComplex] using
      (RingHom.map_det Complex.ofRealHom (sylvesterVecCoeff m n A B)).symm
  have hcomplexZero :
      Matrix.det
        (complexSylvesterVecCoeff (realMatrixToComplex A) (realMatrixToComplex B)) = 0 := by
    rw [(realMatrixToComplex_sylvesterVecCoeff m n A B).symm, hmap, hdet]
    simp
  exact
    (complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair
      (realMatrixToComplex A) (realMatrixToComplex B) hno) hcomplexZero

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the real vec/Kronecker determinant nonsingularity theorem obtained from no
    common supplied complex right eigenpair of the entrywise complexified
    Sylvester factors. -/
theorem H16_eq16_3_sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : ∀ μ : Complex,
      ¬ ((∃ y : Fin m → Complex,
            y ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex A) y = fun i => μ * y i) ∧
          (∃ z : Fin n → Complex,
            z ≠ 0 ∧ Matrix.mulVec (realMatrixToComplex B) z = fun j => μ * z j))) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), named spectral-separation
    form: if the entrywise complexifications of the real Sylvester factors have
    no common complex right eigenvalue, then the real vec/Kronecker Sylvester
    coefficient is nonsingular. -/
theorem sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_eigenpair m n A B hno

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), source-numbered alias for
    the named no-common-complex-right-eigenvalue determinant route. -/
theorem H16_eq16_3_sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B)) :
    Matrix.det (sylvesterVecCoeff m n A B) ≠ 0 :=
  sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue m n A B hno

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    practical endpoint: if the entrywise complexifications of `A` and `B`
    have no common supplied complex right eigenvalue, the vec/Kronecker
    coefficient is nonsingular, so the exact nonsingular inverse supplies the
    practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    scalar endpoint for the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute endpoint: the same practical budget bounds the unnormalized
    max-entry forward error, with no positive denominator hypothesis. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    absolute scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_no_common_complex_right_eigenvalue
            m n A B hno)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    raw computed-residual budget endpoint. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X Xhat Rhat Ru hno hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), spectral-separation
    explicit residual-error-model endpoint. -/
theorem sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X Xhat Rhat Ru hno hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation practical computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation scalar computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute computed-residual certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation absolute scalar certificate. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation raw computed-residual budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source-numbered alias
    for the spectral-separation residual-error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model :=
  sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_error_model

/-- A real matrix intertwining identity remains an intertwining identity after
    entrywise complexification. -/
theorem realMatrixToComplex_intertwining_of_real
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι Real) (B : Matrix κ κ Real)
    (X : Matrix ι κ Real)
    (hX : A * X = X * B) :
    realMatrixToComplex A * realMatrixToComplex X =
      realMatrixToComplex X * realMatrixToComplex B := by
  rw [← realMatrixToComplex_mul A X, hX, realMatrixToComplex_mul X B]

/-- If a real matrix has trivial real kernel, then its entrywise
    complexification has trivial complex kernel. -/
theorem realMatrixToComplex_mulVec_eq_zero_of_real_kernel_trivial
    {ι κ : Type*} [Fintype κ]
    (U : Matrix ι κ Real)
    (hker : ∀ x : κ -> Real, Matrix.mulVec U x = 0 -> x = 0)
    {w : κ -> Complex}
    (hw : Matrix.mulVec (realMatrixToComplex U) w = 0) :
    w = 0 := by
  have hre :
      Matrix.mulVec U (fun k : κ => (w k).re) = 0 := by
    ext i
    have hcoord := congrFun hw i
    have hcoord_re := congrArg Complex.re hcoord
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex] using hcoord_re
  have him :
      Matrix.mulVec U (fun k : κ => (w k).im) = 0 := by
    ext i
    have hcoord := congrFun hw i
    have hcoord_im := congrArg Complex.im hcoord
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex] using hcoord_im
  have hre0 := hker (fun k : κ => (w k).re) hre
  have him0 := hker (fun k : κ => (w k).im) him
  funext k
  have hrek := congrFun hre0 k
  have himk := congrFun him0 k
  exact Complex.ext (by simpa using hrek) (by simpa using himk)

/-- Nonzero complex vectors remain nonzero after a complexified real matrix
    whose real kernel is trivial. -/
theorem realMatrixToComplex_mulVec_ne_zero_of_real_kernel_trivial
    {ι κ : Type*} [Fintype κ]
    (U : Matrix ι κ Real)
    (hker : ∀ x : κ -> Real, Matrix.mulVec U x = 0 -> x = 0)
    {w : κ -> Complex}
    (hw : w ≠ 0) :
    Matrix.mulVec (realMatrixToComplex U) w ≠ 0 := by
  intro hzero
  exact hw
    (realMatrixToComplex_mulVec_eq_zero_of_real_kernel_trivial U hker hzero)

/-- Kernel invariance for a finite real-matrix intertwiner: if `A * X = X * B`,
    then the kernel of `X` is mapped into itself by `B`.  This is the real
    invariant-line algebra needed before the Chapter 16 `2 x 2` real-Schur
    block-separation argument. -/
theorem finiteRealMatrix_intertwiner_kernel_invariant
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι Real) (B : Matrix κ κ Real)
    (X : Matrix ι κ Real)
    (hX : A * X = X * B)
    {x : κ -> Real}
    (hx : Matrix.mulVec X x = 0) :
    Matrix.mulVec X (Matrix.mulVec B x) = 0 := by
  calc
    Matrix.mulVec X (Matrix.mulVec B x) = Matrix.mulVec (X * B) x := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (A * X) x := by rw [← hX]
    _ = Matrix.mulVec A (Matrix.mulVec X x) := by
      rw [← Matrix.mulVec_mulVec]
    _ = 0 := by rw [hx, Matrix.mulVec_zero]

/-- The `2 x 2` determinant of the two real column vectors `x` and `y`. -/
def finTwoVectorDet (x y : Fin 2 -> Real) : Real :=
  x 0 * y 1 - x 1 * y 0

/-- A row vector orthogonal to two linearly independent `Fin 2` vectors is zero. -/
theorem finTwo_row_eq_zero_of_mulVec_two_eq_zero_of_det_ne_zero
    (row x y : Fin 2 -> Real)
    (hx : row 0 * x 0 + row 1 * x 1 = 0)
    (hy : row 0 * y 0 + row 1 * y 1 = 0)
    (hdet : finTwoVectorDet x y ≠ 0) :
    row = 0 := by
  have h0prod : row 0 * finTwoVectorDet x y = 0 := by
    calc
      row 0 * finTwoVectorDet x y =
          y 1 * (row 0 * x 0 + row 1 * x 1) -
            x 1 * (row 0 * y 0 + row 1 * y 1) := by
            simp [finTwoVectorDet]
            ring
      _ = 0 := by rw [hx, hy]; ring
  have h1prod : row 1 * finTwoVectorDet x y = 0 := by
    calc
      row 1 * finTwoVectorDet x y =
          x 0 * (row 0 * y 0 + row 1 * y 1) -
            y 0 * (row 0 * x 0 + row 1 * x 1) := by
            simp [finTwoVectorDet]
            ring
      _ = 0 := by rw [hx, hy]; ring
  have h0 : row 0 = 0 := by
    exact (mul_eq_zero.mp h0prod).resolve_right hdet
  have h1 : row 1 = 0 := by
    exact (mul_eq_zero.mp h1prod).resolve_right hdet
  funext k
  fin_cases k <;> simp [h0, h1]

/-- If a nonzero matrix kills two `Fin 2` vectors, then those vectors have
    zero `2 x 2` determinant. -/
theorem finTwo_det_eq_zero_of_mulVec_two_eq_zero_of_matrix_ne_zero
    {ι : Type*} [Fintype ι]
    (U : Matrix ι (Fin 2) Real)
    (hU : U ≠ 0)
    {x y : Fin 2 -> Real}
    (hx : Matrix.mulVec U x = 0)
    (hy : Matrix.mulVec U y = 0) :
    finTwoVectorDet x y = 0 := by
  by_contra hdet
  apply hU
  ext i k
  have hrow :
      (fun k : Fin 2 => U i k) = 0 := by
    apply finTwo_row_eq_zero_of_mulVec_two_eq_zero_of_det_ne_zero
      (fun k : Fin 2 => U i k) x y
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hy i
    · exact hdet
  exact congrFun hrow k

/-- A zero `2 x 2` determinant with a nonzero first vector means the second
    vector is a real scalar multiple of the first. -/
theorem finTwo_exists_smul_of_det_eq_zero
    {x y : Fin 2 -> Real}
    (hxne : x ≠ 0)
    (hdet : finTwoVectorDet x y = 0) :
    ∃ mu : Real, y = fun k => mu * x k := by
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro hx1
      apply hxne
      funext k
      fin_cases k <;> simp [hx0, hx1]
    refine ⟨y 1 / x 1, ?_⟩
    funext k
    fin_cases k
    · have hy0 : y 0 = 0 := by
        have hprod : x 1 * y 0 = 0 := by
          have hdet' : -(x 1 * y 0) = 0 := by
            simpa [finTwoVectorDet, hx0] using hdet
          linarith
        exact (mul_eq_zero.mp hprod).resolve_left hx1
      simp [hx0, hy0]
    · have hcoord : y 1 = (y 1 / x 1) * x 1 := by
        field_simp [hx1]
      simpa using hcoord
  · refine ⟨y 0 / x 0, ?_⟩
    funext k
    fin_cases k
    · have hcoord : y 0 = (y 0 / x 0) * x 0 := by
        field_simp [hx0]
      simpa using hcoord
    · have hy1 : x 0 * y 1 = x 1 * y 0 := by
        have hdet' : x 0 * y 1 - x 1 * y 0 = 0 := by
          simpa [finTwoVectorDet] using hdet
        linarith
      have hcoord : y 1 = (y 0 / x 0) * x 1 := by
        field_simp [hx0]
        simpa [mul_comm] using hy1
      simpa using hcoord

/-- If a nonzero finite real-matrix intertwiner `A * U = U * J` has a
    nonzero kernel vector, then that vector is a real eigenvector of `J`.
    This is the finite-dimensional no-real-invariant-line bridge needed for
    the `2 x 2` real-Schur block route. -/
theorem finiteRealMatrix_exists_right_eigenvector_of_intertwiner_kernel
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι Real) (J : Matrix (Fin 2) (Fin 2) Real)
    (U : Matrix ι (Fin 2) Real)
    (hX : A * U = U * J)
    (hU : U ≠ 0)
    {x : Fin 2 -> Real}
    (hxne : x ≠ 0)
    (hx : Matrix.mulVec U x = 0) :
    ∃ mu : Real, Matrix.mulVec J x = fun k => mu * x k := by
  have hJx : Matrix.mulVec U (Matrix.mulVec J x) = 0 :=
    finiteRealMatrix_intertwiner_kernel_invariant A J U hX hx
  have hdet :
      finTwoVectorDet x (Matrix.mulVec J x) = 0 :=
    finTwo_det_eq_zero_of_mulVec_two_eq_zero_of_matrix_ne_zero U hU hx hJx
  exact finTwo_exists_smul_of_det_eq_zero hxne hdet

/-- A no-real-eigenvector `2 x 2` right-hand block forces every nonzero
    finite real-matrix intertwiner `A * U = U * J` to have trivial kernel. -/
theorem finiteRealMatrix_intertwiner_mulVec_eq_zero_of_no_real_eigenvector
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι Real) (J : Matrix (Fin 2) (Fin 2) Real)
    (U : Matrix ι (Fin 2) Real)
    (hX : A * U = U * J)
    (hU : U ≠ 0)
    (hno :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ mu : Real, Matrix.mulVec J x = fun k => mu * x k) :
    ∀ x : Fin 2 -> Real, Matrix.mulVec U x = 0 -> x = 0 := by
  intro x hx
  by_contra hxne
  exact hno x hxne
    (finiteRealMatrix_exists_right_eigenvector_of_intertwiner_kernel
      A J U hX hU hxne hx)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    spectral bridge for a supplied adjacent two-column block: a trivial kernel
    for the eigen-equation of the product of the two shifted column
    coefficients proves the characteristic-polynomial nonroot certificate. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_charpoly_ne_zero_of_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
      sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
        (T q p * T p q) = 0) := by
  exact
    finiteMatrix_charpoly_eval_ne_zero_of_mulVec_no_eigenvector
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hker

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    nonroot bridge for a supplied adjacent two-column block: the source-shaped
    characteristic-polynomial exclusion for the shifted product implies the
    no-eigenvector hypothesis used by the active-block solve wrappers. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_charpoly_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hchar :
      Not ((sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p)).charpoly.eval
          (T q p * T p q) = 0)) :
    forall x : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) x =
        (fun i => (T q p * T p q) * x i) ->
      x = 0 := by
  exact
    finiteMatrix_mulVec_no_eigenvector_of_charpoly_eval_ne_zero
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hchar

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    determinant bridge for a supplied adjacent two-column block: a nonsingular
    shifted product `(A - T_qq I) (A - T_pp I) - T_qp T_pq I` gives the
    no-eigenvector hypothesis needed by the existing block determinant and
    solve consequences. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_product_shift_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det
        (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p) -
          Matrix.scalar (Fin m) (T q p * T p q)) = 0)) :
    forall x : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) x =
        (fun i => (T q p * T p q) * x i) ->
      x = 0 := by
  exact
    finiteMatrix_mulVec_no_eigenvector_of_det_sub_scalar_ne_zero
      (sylvesterTriangularShiftedCoeff m A (T q q) *
        sylvesterTriangularShiftedCoeff m A (T p p))
      (T q p * T p q) hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    spectrum bridge for a supplied adjacent two-column block: if the
    product-shift eigen-equation
    `(A - T_qq I) (A - T_pp I) x = (T_qp T_pq) x` has only the zero solution,
    then the full real-Schur two-column block coefficient is nonsingular. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_charpoly
  exact
    sylvesterTwoColumnBlockCoeff_product_shift_charpoly_ne_zero_of_no_eigenvector
      m n A T p q hker

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    certificate through the no-eigenvector bridge: nonsingularity of the
    product-shift matrix gives nonsingularity of the supplied two-column block
    coefficient via the same product-shift kernel surface used by later solve
    wrappers. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det
        (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p) -
          Matrix.scalar (Fin m) (T q p * T p q)) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
  exact
    sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_product_shift_det_ne_zero
      m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block action
    of the left Sylvester factor on the two active columns.  This packages
    the exact operation `A [u v]` as one block-vector matrix action; it is
    only algebraic infrastructure for the real-Schur two-column route. -/
noncomputable def sylvesterTwoColumnBlockLeftAction (m : Nat)
    (A : RMatFn m m) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks (Matrix.of A) 0 0 (Matrix.of A)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block action
    of the supplied adjacent `2 x 2` real-Schur diagonal block on the two
    active columns.  The top-right and bottom-left scalar identity blocks
    follow the column equations
    `A u = T_pp u + T_qp v` and `A v = T_pq u + T_qq v`. -/
noncomputable def sylvesterTwoColumnBlockSchurAction (m n : Nat)
    (T : RMatFn n n) (p q : Fin n) :
    Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real :=
  Matrix.fromBlocks
    ((T p p) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T q p) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T p q) • (1 : Matrix (Fin m) (Fin m) Real))
    ((T q q) • (1 : Matrix (Fin m) (Fin m) Real))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), two active
    columns packaged as an `m x 2` matrix.  Column `0` is `u` and column `1`
    is `v`; this is the standard matrix-intertwining shape behind the
    block-action certificate. -/
def sylvesterTwoColumnBlockColumnPair (m : Nat)
    (u v : Fin m -> Real) : Matrix (Fin m) (Fin 2) Real :=
  fun i k => if k = 0 then u i else v i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), the supplied
    adjacent real `2 x 2` Schur block acting on the two active columns. -/
def sylvesterTwoColumnRealSchurBlock (n : Nat)
    (T : RMatFn n n) (p q : Fin n) : Matrix (Fin 2) (Fin 2) Real :=
  fun r c =>
    if r = 0 then
      if c = 0 then T p p else T p q
    else
      if c = 0 then T q p else T q q

/-- A concrete complex eigenvector candidate for the adjacent `2 x 2` block,
    using a supplied complex root `mu` and the nonzero subdiagonal entry. -/
def sylvesterTwoColumnRealSchurBlockComplexRootVector (n : Nat)
    (T : RMatFn n n) (p q : Fin n) (mu : Complex) :
    Fin 2 -> Complex :=
  fun k => if k = 0 then mu - (T q q : Complex) else (T q p : Complex)

/-- The concrete complex root vector is nonzero when the subdiagonal entry of
    the adjacent `2 x 2` block is nonzero. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (mu : Complex)
    (hsub : T q p ≠ 0) :
    sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero (1 : Fin 2)
  have hc : ((T q p : Real) : Complex) = 0 := by
    simpa [sylvesterTwoColumnRealSchurBlockComplexRootVector] using hentry
  exact hsub (Complex.ofReal_eq_zero.mp hc)

/-- If `mu` is a supplied complex root of the characteristic equation of the
    adjacent `2 x 2` block and the subdiagonal entry is used in the concrete
    vector, then the vector is a complex eigenvector of the block. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (mu : Complex)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0) :
    Matrix.mulVec
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu) =
      fun k => mu *
        sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu k := by
  funext k
  fin_cases k
  · have hcoord :
        ((T p p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T p q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * (mu - ((T q q : Real) : Complex)) := by
      calc
        ((T p p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T p q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * (mu - ((T q q : Real) : Complex)) -
            ((((T p p : Real) : Complex) - mu) *
              (((T q q : Real) : Complex) - mu) -
                ((T p q : Real) : Complex) * ((T q p : Real) : Complex)) := by
          ring
        _ = mu * (mu - ((T q q : Real) : Complex)) := by rw [hroot, sub_zero]
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex,
      sylvesterTwoColumnRealSchurBlock,
      sylvesterTwoColumnRealSchurBlockComplexRootVector,
      Fin.sum_univ_two] using hcoord
  · have hcoord :
        ((T q p : Real) : Complex) * (mu - ((T q q : Real) : Complex)) +
            ((T q q : Real) : Complex) * ((T q p : Real) : Complex) =
          mu * ((T q p : Real) : Complex) := by
      ring
    simpa [Matrix.mulVec, dotProduct, realMatrixToComplex,
      sylvesterTwoColumnRealSchurBlock,
      sylvesterTwoColumnRealSchurBlockComplexRootVector,
      Fin.sum_univ_two] using hcoord

/-- The standard complex root of the adjacent real `2 x 2` block when the
    real discriminant is negative and `delta` supplies its positive square
    root magnitude. -/
noncomputable def sylvesterTwoColumnRealSchurBlockComplexRoot (n : Nat)
    (T : RMatFn n n) (p q : Fin n) (delta : Real) : Complex :=
  ((((T p p + T q q) / 2 : Real) : Complex) +
    Complex.I * (((delta / 2 : Real) : Complex)))

/-- The standard complex root satisfies the characteristic equation of the
    adjacent real `2 x 2` block whenever `delta^2` is the negative
    discriminant. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (delta : Real)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p)) :
    (((T p p : Real) : Complex) -
        sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) *
      (((T q q : Real) : Complex) -
        sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) -
        ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0 := by
  apply Complex.ext
  · simp [sylvesterTwoColumnRealSchurBlockComplexRoot, Complex.mul_re,
      Complex.mul_im]
    nlinarith [hdelta]
  · simp [sylvesterTwoColumnRealSchurBlockComplexRoot, Complex.mul_re,
      Complex.mul_im]
    ring

/-- A nonzero negative-discriminant square-root certificate rules out real
    eigenlines for the adjacent `2 x 2` block. -/
theorem sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (delta : Real)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0) :
    ∀ x : Fin 2 -> Real, x ≠ 0 ->
      ¬ ∃ nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k := by
  intro x hxne hEig
  rcases hEig with ⟨nu, hnu⟩
  have hxzero :
      Matrix.mulVec
          (sylvesterTwoColumnRealSchurBlock n T p q -
            Matrix.scalar (Fin 2) nu) x = 0 := by
    funext k
    have hk := congrFun hnu k
    have hcoord :
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x k -
            nu * x k = 0 := by
      rw [hk]
      ring
    simpa [Matrix.sub_mulVec, Matrix.scalar_apply] using hcoord
  have hdet :
      Matrix.det
          (sylvesterTwoColumnRealSchurBlock n T p q -
            Matrix.scalar (Fin 2) nu) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hxne, hxzero⟩
  have hroot :
      (T p p - nu) * (T q q - nu) - T p q * T q p = 0 := by
    simpa [sylvesterTwoColumnRealSchurBlock, Matrix.det_fin_two,
      Matrix.scalar_apply] using hdet
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p =
        (T p p + T q q - 2 * nu) ^ 2 := by
    nlinarith [hroot]
  have hsum :
      delta ^ 2 + (T p p + T q q - 2 * nu) ^ 2 = 0 := by
    nlinarith [hdelta, hdisc]
  have hdelta_pos : 0 < delta ^ 2 := sq_pos_of_ne_zero hdelta_ne
  have hsquare_nonneg : 0 ≤ (T p p + T q q - 2 * nu) ^ 2 := sq_nonneg _
  nlinarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), converse
    two-by-two spectral certificate: a nonnegative real discriminant for the
    adjacent real Schur block gives a concrete real eigenline.  This is the
    algebraic obstruction to treating such a block as a genuine irreducible
    real `2 x 2` block. -/
theorem sylvesterTwoColumnRealSchurBlock_exists_real_eigenvector_of_disc_nonneg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      0 ≤ (T p p - T q q) ^ 2 + 4 * T p q * T q p) :
    exists x : Fin 2 -> Real, x ≠ 0 ∧
      exists nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k := by
  by_cases hsub : T q p = 0
  · let x : Fin 2 -> Real := fun k => if k = 0 then 1 else 0
    refine ⟨x, ?_, T p p, ?_⟩
    · intro hx
      have hcoord := congrFun hx (0 : Fin 2)
      norm_num [x] at hcoord
    · funext k
      fin_cases k
      · simp [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock]
      · simp [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          hsub]
  · let disc : Real := (T p p - T q q) ^ 2 + 4 * T p q * T q p
    let nu : Real := (T p p + T q q + Real.sqrt disc) / 2
    let x : Fin 2 -> Real := fun k => if k = 0 then nu - T q q else T q p
    have hdisc_nonneg : 0 ≤ disc := by
      dsimp [disc]
      exact hdisc
    have hsqrt : (Real.sqrt disc) ^ 2 = disc := Real.sq_sqrt hdisc_nonneg
    have hroot : (T p p - nu) * (T q q - nu) - T p q * T q p = 0 := by
      dsimp [nu, disc] at hsqrt ⊢
      nlinarith [hsqrt]
    refine ⟨x, ?_, nu, ?_⟩
    · intro hx
      have hcoord := congrFun hx (1 : Fin 2)
      exact hsub (by simpa [x] using hcoord)
    · funext k
      fin_cases k
      · have hcoord :
            T p p * (nu - T q q) + T p q * T q p =
              nu * (nu - T q q) := by
          nlinarith [hroot]
        simpa [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          Fin.sum_univ_two] using hcoord
      · have hcoord :
            T q p * (nu - T q q) + T q q * T q p =
              nu * T q p := by
          ring
        simpa [x, Matrix.mulVec, dotProduct, sylvesterTwoColumnRealSchurBlock,
          Fin.sum_univ_two] using hcoord

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), irreducible
    real `2 x 2` block discriminant certificate: if the adjacent real Schur
    block has no nonzero real eigenline, then its discriminant is negative. -/
theorem sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)) :
    (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
  by_contra hnot
  have hdisc :
      0 ≤ (T p p - T q q) ^ 2 + 4 * T p q * T q p := by
    linarith
  rcases sylvesterTwoColumnRealSchurBlock_exists_real_eigenvector_of_disc_nonneg
      n T p q hdisc with ⟨x, hxne, nu, hnu⟩
  exact hno x hxne ⟨nu, hnu⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), matrix
    intertwining form: the coupled active-column equations are equivalent to
    `A * U = U * J`, where `U` is the two-column matrix `(u, v)` and `J` is
    the supplied adjacent real `2 x 2` Schur block.  This is the standard
    spectral-facing target for the still-open complex separation proof. -/
theorem sylvesterTwoColumnBlock_coupled_block_action_iff_columnPair_intertwining
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    (Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i)) ↔
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q := by
  constructor
  · intro h
    rcases h with ⟨hu, hv⟩
    ext i k
    fin_cases k
    · have hi := congrFun hu i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
    · have hi := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
  · intro h
    constructor
    · funext i
      have hi := congrFun (congrFun h i) (0 : Fin 2)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi
    · funext i
      have hi := congrFun (congrFun h i) (1 : Fin 2)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        sylvesterTwoColumnBlockColumnPair, sylvesterTwoColumnRealSchurBlock,
        Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), complexified
    two-column intertwining bridge: a real identity `A * U = U * J` for the
    active two-column matrix and supplied adjacent real Schur block remains
    valid after entrywise complexification, so it can be consumed by complex
    spectral/eigenvector lemmas. -/
theorem sylvesterTwoColumnBlock_columnPair_intertwining_complexification
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q) :
    realMatrixToComplex (Matrix.of A) *
        realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) =
      realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) *
        realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) :=
  realMatrixToComplex_intertwining_of_real
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), kernel
    invariance for a two-column intertwiner: if the active column pair
    satisfies `A * U = U * J`, then the real kernel of `U` is invariant under
    the supplied adjacent `2 x 2` Schur block `J`.  This is a preparatory
    algebraic step for ruling out nonzero block-action witnesses from
    irreducible real-Schur block separation. -/
theorem sylvesterTwoColumnBlock_columnPair_kernel_invariant
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    {x : Fin 2 -> Real}
    (hx :
      Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v) x = 0) :
    Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v)
        (Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x) = 0 :=
  finiteRealMatrix_intertwiner_kernel_invariant
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX hx

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), no-real-line
    consequence for the two-column intertwiner: if the supplied adjacent
    `2 x 2` Schur block has no real eigenvector and the active column-pair
    map is nonzero, then the column-pair map has trivial real kernel.  This
    is the source-shaped irreducibility dependency before deriving the full
    no-block-action certificate from complex spectral separation. -/
theorem sylvesterTwoColumnBlock_columnPair_mulVec_eq_zero_of_no_real_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    (hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0)
    (hno :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ mu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => mu * x k) :
    ∀ x : Fin 2 -> Real,
      Matrix.mulVec (sylvesterTwoColumnBlockColumnPair m u v) x = 0 ->
        x = 0 :=
  finiteRealMatrix_intertwiner_mulVec_eq_zero_of_no_real_eigenvector
    (Matrix.of A) (sylvesterTwoColumnRealSchurBlock n T p q)
    (sylvesterTwoColumnBlockColumnPair m u v) hX hU hno

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), complexified
    nonzero-image bridge for the two-column intertwiner: if the adjacent
    `2 x 2` real Schur block has no real eigenvector and the active
    column-pair map is nonzero, then every nonzero complex vector has nonzero
    image under the complexified column-pair map. -/
theorem sylvesterTwoColumnBlock_columnPair_complex_mulVec_ne_zero_of_no_real_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real)
    (hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q)
    (hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0)
    (hno :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ mu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => mu * x k)
    {w : Fin 2 -> Complex}
    (hw : w ≠ 0) :
    Matrix.mulVec
        (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v)) w ≠ 0 :=
  realMatrixToComplex_mulVec_ne_zero_of_real_kernel_trivial
    (sylvesterTwoColumnBlockColumnPair m u v)
    (sylvesterTwoColumnBlock_columnPair_mulVec_eq_zero_of_no_real_eigenvector
      m n A T p q u v hX hU hno)
    hw

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-action
    packaging: the two coupled active-column equations are equivalent to
    equality of the left `A` action and the supplied `2 x 2` Schur-block
    action on the concatenated vector `(u, v)`.  This is the algebraic target
    that a future real-Schur spectral-separation theorem can rule out. -/
theorem sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    (Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i)) ↔
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A)
          (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) := by
  constructor
  · intro h
    rcases h with ⟨hu, hv⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hu i
        rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
          Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inl, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.add_apply]
        simpa using hi
    | inr i =>
        have hi := congrFun hv i
        rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
          Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inr, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.add_apply]
        simpa [add_comm, add_left_comm, add_assoc] using hi
  · intro h
    constructor
    · funext i
      have hi := congrFun h (Sum.inl i)
      rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
        Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inl, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.add_apply] at hi
      simpa using hi
    · funext i
      have hi := congrFun h (Sum.inr i)
      rw [sylvesterTwoColumnBlockLeftAction, sylvesterTwoColumnBlockSchurAction,
        Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inr, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.add_apply] at hi
      simpa [add_comm, add_left_comm, add_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), active-block
    kernel packaging: the supplied two-column block coefficient kills the
    concatenated vector `(u, v)` exactly when the two coupled column-action
    equations hold. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_sumElim_eq_zero_iff_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (u v : Fin m -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim u v) = 0 ↔
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) := by
  constructor
  · intro hzero
    constructor
    · funext i
      have hi := congrFun hzero (Sum.inl i)
      have hi' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i +
              (-(T q p)) * v i = 0 := by
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec] using hi
      have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
      have hP' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i =
            Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
        simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
      linarith
    · funext i
      have hi := congrFun hzero (Sum.inr i)
      have hi' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i +
              (-(T p q)) * u i = 0 := by
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, add_comm, add_left_comm, add_assoc]
          using hi
      have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
      have hQ' :
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i =
            Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
        simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
      linarith
  · intro haction
    rcases haction with ⟨hu, hv⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hu i
        have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
        have hP' :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i =
              Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
          simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
        have hgoal :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T p p)) u i +
                (-(T q p)) * v i = 0 := by
          linarith
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec] using hgoal
    | inr i =>
        have hi := congrFun hv i
        have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
        have hQ' :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i =
              Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
          simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
        have hgoal :
            Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T q q)) v i +
                (-(T p q)) * u i = 0 := by
          linarith
        simpa [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, add_comm, add_left_comm, add_assoc]
          using hgoal

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-kernel
    separation packaging: the supplied two-column coefficient has a nonzero
    kernel vector exactly when the left `A` block action agrees with the
    supplied `2 x 2` Schur-block action on a nonzero concatenated vector. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_leftAction_eq_schurAction
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 ↔
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z := by
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  have hz : z = Sum.elim u v := by
    funext r
    cases r <;> rfl
  rw [hz]
  exact
    (sylvesterTwoColumnBlockCoeff_mulVec_sumElim_eq_zero_iff_coupled_block_action
      m n A T p q u v).trans
      (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
        m n A T p q u v)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    block-action separation certificate: if no nonzero concatenated two-column
    vector makes the left `A` action agree with the supplied `2 x 2`
    Schur-block action, then the supplied two-column block coefficient is
    nonsingular.  This is the determinant-facing form of the still-open
    spectral-separation target. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hno :
      ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  obtain ⟨z, hz_ne, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hno z hz_ne
    ((sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_leftAction_eq_schurAction
      m n A T p q z).mp hzero)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    complex-separation bridge to the no-block-action certificate: if the
    adjacent real `2 x 2` block has no real eigenline, has a supplied complex
    eigenpair `(mu, w)`, and `A` has no complex eigenvector for that same
    `mu`, then no nonzero two-column block-action witness can exist. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex) (w : Fin 2 -> Complex)
    (hwne : w ≠ 0)
    (hwJ :
      Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
        fun k => mu * w k)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z := by
  intro z hz hblock
  let u : Fin m -> Real := fun i => z (Sum.inl i)
  let v : Fin m -> Real := fun i => z (Sum.inr i)
  have hz_sum : z = Sum.elim u v := by
    funext r
    cases r <;> rfl
  have hblock_uv :
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) := by
    simpa [hz_sum] using hblock
  have hcoupled :
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
        Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
      m n A T p q u v).mpr hblock_uv
  have hX :
      Matrix.of A * sylvesterTwoColumnBlockColumnPair m u v =
        sylvesterTwoColumnBlockColumnPair m u v *
          sylvesterTwoColumnRealSchurBlock n T p q :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_columnPair_intertwining
      m n A T p q u v).mp hcoupled
  have hU : sylvesterTwoColumnBlockColumnPair m u v ≠ 0 := by
    intro hzero
    apply hz
    rw [hz_sum]
    funext r
    cases r with
    | inl i =>
        have hentry := congrFun (congrFun hzero i) (0 : Fin 2)
        simpa [u, sylvesterTwoColumnBlockColumnPair] using hentry
    | inr i =>
        have hentry := congrFun (congrFun hzero i) (1 : Fin 2)
        simpa [v, sylvesterTwoColumnBlockColumnPair] using hentry
  have hXc :
      realMatrixToComplex (Matrix.of A) *
          realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) =
        realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v) *
          realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q) :=
    sylvesterTwoColumnBlock_columnPair_intertwining_complexification
      m n A T p q u v hX
  have hXw :
      Matrix.mulVec
          (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v)) w ≠ 0 :=
    sylvesterTwoColumnBlock_columnPair_complex_mulVec_ne_zero_of_no_real_eigenvector
      m n A T p q u v hX hU hnoReal hwne
  exact hnoA
    (finiteComplexMatrix_exists_mulVec_eigenpair_of_intertwiner_image_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (realMatrixToComplex (sylvesterTwoColumnBlockColumnPair m u v))
      mu w hXc hwJ hXw)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of a supplied complex eigenpair/separation certificate for the
    adjacent real `2 x 2` block.  This is still a supplied-certificates route:
    it does not construct the complex eigenpair or no-common-spectrum
    hypothesis from a full Schur spectral theorem. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_eigenpair_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex) (w : Fin 2 -> Complex)
    (hwne : w ≠ 0)
    (hwJ :
      Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
        fun k => mu * w k)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
      m n A T p q mu w hwne hwJ hnoReal hnoA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), root-based
    complex-separation bridge to the no-block-action certificate: a supplied
    complex root of the adjacent `2 x 2` characteristic equation gives the
    concrete eigenvector used by the complex-separation bridge. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex)
    (hsub : T q p ≠ 0)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z :=
  sylvesterTwoColumnBlock_no_block_action_of_complex_eigenpair_separation
    m n A T p q mu
    (sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q mu)
    (sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero n T p q mu hsub)
    (sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec n T p q mu hroot)
    hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of a supplied complex root/separation certificate for the
    adjacent real `2 x 2` block. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (mu : Complex)
    (hsub : T q p ≠ 0)
    (hroot :
      (((T p p : Real) : Complex) - mu) *
        (((T q q : Real) : Complex) - mu) -
          ((T p q : Real) : Complex) * ((T q p : Real) : Complex) = 0)
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => mu * y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
      m n A T p q mu hsub hroot hnoReal hnoA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from a supplied negative-discriminant square-root certificate:
    `delta` constructs the standard complex root of the adjacent real `2 x 2`
    block, and the root-based separation bridge proves nonsingularity of the
    active block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hnoReal :
      ∀ x : Fin 2 -> Real, x ≠ 0 ->
        ¬ ∃ nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_root_separation
    m n A T p q
    (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
    hsub
    (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
      n T p q delta hdelta)
    hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from a nonzero negative-discriminant square-root certificate:
    the same certificate supplies both the standard complex root and the
    no-real-eigenline hypothesis for the adjacent real `2 x 2` block. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_no_real_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0)
    (hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_separation
    m n A T p q delta hsub hdelta
    (sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
      n T p q delta hdelta hdelta_ne)
    hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence from fully determinant-shaped supplied spectral separation:
    a nonzero shifted complex determinant for `A` at the constructed
    negative-discriminant root supplies the remaining no-common-eigenvalue
    exclusion used by the delta-root route. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (delta : Real)
    (hsub : T q p ≠ 0)
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : delta ≠ 0)
    (hdetA :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0)) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
  sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_no_real_separation
    m n A T p q delta hsub hdelta hdelta_ne
    (finiteComplexMatrix_no_eigenpair_of_det_sub_scalar_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), scalar
    discriminant fact for a genuine adjacent real `2 x 2` block: if the real
    block discriminant is negative, then the subdiagonal entry `T q p` cannot
    vanish.  This is the small algebraic certificate needed by the concrete
    complex-root vector `(mu - T_qq, T_qp)`. -/
theorem sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    Not (T q p = 0) := by
  intro hzero_qp
  have hsq : 0 <= (T p p - T q q) ^ 2 :=
    sq_nonneg (T p p - T q q)
  have hdisc_nonneg :
      0 <= (T p p - T q q) ^ 2 + 4 * T p q * T q p := by
    simpa [hzero_qp] using hsq
  linarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), negative
    discriminant implies no real eigenline for the adjacent real `2 x 2`
    block.  The proof instantiates the existing nonzero square-root route with
    `delta = sqrt (-disc)`. -/
theorem sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    forall x : Fin 2 -> Real, x ≠ 0 ->
      Not (exists nu : Real,
        Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
          fun k => nu * x k) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hdelta_ne : Not (delta = 0) := by
    intro hzero_delta
    rw [hzero_delta] at hdelta
    norm_num at hdelta
    linarith
  exact
    sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_delta_sq_ne_zero
      n T p q delta hdelta hdelta_ne

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): if an adjacent
    real Schur `2 x 2` block has negative discriminant, the standard complex
    root `sqrt (-disc)` is a supplied complex right eigenvalue of the
    complexified block. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
    (n : Nat) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0) :
    HasComplexRightEigenvalue
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
        (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p)))) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  exact
    ⟨sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q
        (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta),
      sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hsub,
      sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
        (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
          n T p q delta hdelta)⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): a
    no-common-complex-eigenpair hypothesis between the adjacent real-Schur
    block and the left matrix supplies the shifted determinant certificate at
    the standard complex root `sqrt (-disc)`.  This is the source-facing route
    that remains after the constructed real-quasi-Schur API supplies the
    negative-discriminant side. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      ∀ mu : Complex,
        (∃ w : Fin 2 -> Complex,
          w ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
              fun k => mu * w k) ->
        ¬ ∃ y : Fin m -> Complex,
          y ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
              fun i => mu * y i) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hblockEig :
      ∃ w : Fin 2 -> Complex,
        w ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
            fun k => sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta * w k :=
    ⟨sylvesterTwoColumnRealSchurBlockComplexRootVector n T p q
        (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta),
      sylvesterTwoColumnRealSchurBlockComplexRootVector_ne_zero
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hsub,
      sylvesterTwoColumnRealSchurBlockComplexRootVector_mulVec
        n T p q (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
        (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
          n T p q delta hdelta)⟩
  have hnoA :
      ¬ ∃ y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i => sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta * y i :=
    hnoCommon (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta) hblockEig
  have hdet :=
    finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_eigenpair
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hnoA
  simpa [delta] using hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): named
    no-common-complex-right-eigenvalue version of the adjacent real-Schur
    block shifted determinant certificate. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  exact
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
      m n A T p q hdisc
      (fun mu hblock hA => hnoCommon mu ⟨hblock, hA⟩)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): left-matrix-first
    no-common-complex-right-eigenvalue version of the adjacent real-Schur
    block shifted determinant certificate.  The block eigenvalue at the
    standard complex root is produced locally from the negative discriminant. -/
theorem sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) := by
  exact
    finiteComplexMatrix_det_sub_scalar_ne_zero_of_no_common_right_eigenvalue_left
      (realMatrixToComplex (Matrix.of A))
      (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
        (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))
      hnoCommon
      (sylvesterTwoColumnRealSchurBlockComplexRoot_hasComplexRightEigenvalue_of_disc_neg
        n T p q hdisc)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    no-block-action certificate from a negative real discriminant and a
    shifted complex determinant separation certificate for `A`.  This is the
    source-shaped spectral obstruction before taking determinants of the
    active two-column coefficient. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) := by
  let delta : Real := Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))
  have hsub : Not (T q p = 0) :=
    sylvesterTwoColumnRealSchurBlock_subdiagonal_ne_zero_of_disc_neg
      n T p q hdisc
  have hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p) := by
    dsimp [delta]
    rw [Real.sq_sqrt]
    linarith
  have hnoReal :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k) :=
    sylvesterTwoColumnRealSchurBlock_no_real_eigenvector_of_disc_neg
      n T p q hdisc
  have hdetA_delta :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0) := by
    simpa [delta] using hdetA
  have hnoA :
      Not (exists y : Fin m -> Complex,
        y ≠ 0 ∧
          Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
            fun i =>
              sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta *
                y i) :=
    finiteComplexMatrix_no_eigenpair_of_det_sub_scalar_ne_zero
      (realMatrixToComplex (Matrix.of A))
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hdetA_delta
  exact
    sylvesterTwoColumnBlock_no_block_action_of_complex_root_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)
      hsub
      (sylvesterTwoColumnRealSchurBlockComplexRoot_root_of_delta_sq
        n T p q delta hdelta)
      hnoReal hnoA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), explicit
    source-shaped separation certificate for a supplied adjacent real
    `2 x 2` Schur block: the block discriminant is negative and the
    complexified left coefficient has nonzero shifted determinant at the
    standard complex root `sqrt (-disc)`.  This predicate records concrete
    spectral data; it is not the no-block-action conclusion itself. -/
def IsSylvesterTwoColumnRealSchurBlockSeparation
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) : Prop :=
  (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 ∧
    Not
      ((Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
              (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), direct producer
    for the explicit real-Schur block-separation predicate from the two
    spectral certificates that a stronger real-Schur block API should export:
    negative discriminant for the adjacent `2 x 2` block and shifted complex
    determinant separation for `A`. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q :=
  ⟨hdisc, hdetA⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), direct producer
    for the explicit real-Schur block-separation predicate from an
    irreducibility-shaped `2 x 2` block certificate: no nonzero real
    eigenline supplies the negative discriminant, while the shifted complex
    determinant separation for `A` remains explicit. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_no_real_eigenvector_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k))
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q := by
  exact
    sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
        n T p q hno)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), canonical
    real `2 x 2` rotation-scaling block algebra: if the adjacent block has
    entries `[[alpha, beta], [-beta, alpha]]` in the `(p,q)` order and
    `beta != 0`, then its real Schur discriminant is negative.  This is the
    local algebraic bridge needed by a future stronger real-Schur export. -/
theorem sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
    (n : Nat) (T : RMatFn n n) (p q : Fin n) (alpha beta : Real)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0) :
    (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
  have hbeta_sq_pos : 0 < beta ^ 2 := sq_pos_of_ne_zero hbeta
  rw [hpp, hqq, hpq, hqp]
  nlinarith

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), canonical
    real `2 x 2` block producer for the explicit block-separation predicate:
    rotation-scaling block entries provide the negative discriminant, while
    the shifted determinant separation for `A` remains an explicit spectral
    certificate. -/
theorem sylvesterTwoColumnRealSchurBlock_separation_of_rotation_scaling_entries
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n) (alpha beta : Real)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q := by
  exact
    sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
      m n A T p q
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
        n T p q alpha beta hpp hqq hpq hqp hbeta)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), named
    no-block-action bridge from the explicit real-Schur block-separation
    certificate.  The remaining open source work is to derive
    `IsSylvesterTwoColumnRealSchurBlockSeparation` automatically from the
    stronger real-Schur block API, not from the current block-map predicate
    alone. -/
theorem sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q) :
    forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
      Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) := by
  exact sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
    m n A T p q hsep.1 hsep.2

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    consequence of the explicit real-Schur block-separation certificate. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_realSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
      m n A T p q hsep)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur two-column separation certificate: the exported
    quasi-Schur block-map data identifies an adjacent same-block pair, and
    the block carries the explicit real-Schur separation certificate used by
    the no-block-action bridge.  This is a convenient supplied-certificate
    surface; deriving it from `real_quasi_schur_blocks` alone remains open
    because that API exports only block size and below-block zeros. -/
def IsSylvesterTwoColumnRealQuasiSchurBlockSeparation
    (m n : Nat) (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n) : Prop :=
  Monotone pmap ∧
    (forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2) ∧
    (forall i j : Fin n, pmap j < pmap i -> T i j = 0) ∧
    q.val = p.val + 1 ∧
    pmap p = pmap q ∧
    IsSylvesterTwoColumnRealSchurBlockSeparation m n A T p q

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from block-map data, adjacent
    same-block provenance, a negative-discriminant certificate for the block,
    and shifted determinant separation for `A`.  This is the direct adapter
    for a future strengthened `real_quasi_schur_blocks` theorem that exports
    irreducible `2 x 2` block discriminants. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    ⟨hmono, hcard, hzero, hpq_adj, hsame,
      sylvesterTwoColumnRealSchurBlock_separation_of_disc_det_separation
        m n A T p q hdisc hdetA⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from block-map data, adjacent
    same-block provenance, a no-real-eigenline certificate for the adjacent
    `2 x 2` block, and shifted determinant separation for `A`. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_no_real_eigenvector_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k))
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_no_real_eigenvector
        n T p q hno)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur separation producer from the constructed spectral
    certificate exported by `real_quasi_schur_blocks_twoBlockSpectral`, plus
    the still-explicit shifted determinant separation for the left matrix. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  have hno :
      forall x : Fin 2 -> Real, x ≠ 0 ->
        Not (exists nu : Real,
          Matrix.mulVec (sylvesterTwoColumnRealSchurBlock n T p q) x =
            fun k => nu * x k) := by
    simpa [HasRealQuasiSchurTwoBlockSpectral, MatrixNoRealEigenline,
      principalTwoBlock, sylvesterTwoColumnRealSchurBlock, Matrix.of_apply] using
      (hspectral p q hpq_adj hsame).1
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_no_real_eigenvector_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hno hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur block-separation producer from canonical rotation-scaling
    entries for the adjacent `2 x 2` block.  The current `real_quasi_schur_blocks`
    API does not export these entries; this theorem closes the algebra once a
    stronger real-Schur construction provides them. -/
theorem sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_rotation_scaling_entries
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n) (alpha beta : Real)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpp : T p p = alpha)
    (hqq : T q q = alpha)
    (hpq_entry : T p q = beta)
    (hqp : T q p = -beta)
    (hbeta : beta ≠ 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q := by
  exact
    sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame
      (sylvesterTwoColumnRealSchurBlock_disc_neg_of_rotation_scaling_entries
        n T p q alpha beta hpp hqq hpq_entry hqp hbeta)
      hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), bundled
    real-quasi-Schur block-separation bridge to the adjacent-block predicate
    and no-block-action certificate. -/
theorem sylvesterTwoColumnBlock_block_and_no_block_action_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      (forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z)) := by
  rcases hsep with ⟨hmono, hcard, hzero, hpq, hsame, hblockSep⟩
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlock_no_block_action_of_realSchur_block_separation
      m n A T p q hblockSep

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), determinant
    consequence of the bundled real-quasi-Schur block-separation certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hcert :=
    sylvesterTwoColumnBlock_block_and_no_block_action_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep
  exact ⟨hcert.1,
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
      m n A T p q hcert.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), determinant
    consequence of the constructed real-quasi-Schur two-block spectral
    certificate plus shifted determinant separation. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q
      (sylvesterTwoColumnRealQuasiSchurBlockSeparation_of_twoBlockSpectral_det_separation
        m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): the constructed
    real-quasi-Schur two-block spectral certificate plus a global
    no-common-complex-eigenpair hypothesis for the adjacent block supplies the
    active two-column block shape and determinant nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_eigenpair
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      ∀ mu : Complex,
        (∃ w : Fin 2 -> Complex,
          w ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q)) w =
              fun k => mu * w k) ->
        ¬ ∃ y : Fin m -> Complex,
          y ≠ 0 ∧
            Matrix.mulVec (realMatrixToComplex (Matrix.of A)) y =
              fun i => mu * y i) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_eigenpair
      m n A T p q hdisc hnoCommon
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): named
    no-common-complex-right-eigenvalue version of the two-block spectral route
    to adjacent active-block shape and determinant nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_right_eigenvalue
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))
        (realMatrixToComplex (Matrix.of A))) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_eigenpair
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral
      (fun mu hblock hA => hnoCommon mu ⟨hblock, hA⟩)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8): left-matrix-first
    no-common-complex-right-eigenvalue version of the constructed
    two-block-spectral route to adjacent active-block shape and determinant
    nonsingularity. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_no_common_complex_right_eigenvalue_left
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq_adj : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hspectral : HasRealQuasiSchurTwoBlockSpectral (Matrix.of T) pmap)
    (hnoCommon :
      NoCommonComplexRightEigenvalue
        (realMatrixToComplex (Matrix.of A))
        (realMatrixToComplex (sylvesterTwoColumnRealSchurBlock n T p q))) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0 := by
    simpa [Matrix.of_apply] using (hspectral p q hpq_adj hsame).2
  have hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0)) :=
    sylvesterTwoColumnRealSchurBlockComplexRoot_det_separation_of_disc_no_common_complex_right_eigenvalue_left
      m n A T p q hdisc hnoCommon
  exact
    sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_twoBlockSpectral_det_separation
      m n A T pmap p q hmono hcard hzero hpq_adj hsame hspectral hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), direct
    determinant-shaped complex-separation route from a negative real
    discriminant: `sqrt (-disc)` supplies the complex root and no-real-line
    certificate, while the shifted complex determinant for `A` remains an
    explicit separation hypothesis. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
    m n A T p q
    (sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
      m n A T p q hdisc hdetA)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block determinant-shaped complex-separation certificate: an adjacent
    same-labelled block in the exported quasi-Schur block map supplies the
    two-column zero pattern, while a supplied negative-discriminant square-root
    and shifted complex determinant separation certificate make the active
    two-column block coefficient nonsingular.  This packages the proved
    complex-root route with the structural quasi-Schur block-map data; it does
    not construct the spectral certificates from the quasi-Schur predicate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_complex_delta_root_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (delta : Real)
    (hsub : Not (T q p = 0))
    (hdelta :
      delta ^ 2 =
        -((T p p - T q q) ^ 2 + 4 * T p q * T q p))
    (hdelta_ne : Not (delta = 0))
    (hdetA :
      Not (Matrix.det
        (realMatrixToComplex (Matrix.of A) -
          Matrix.scalar (Fin m)
            (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q delta)) = 0)) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_complex_delta_root_det_separation
      m n A T p q delta hsub hdelta hdelta_ne hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block no-block-action certificate from a negative real discriminant
    and a shifted complex determinant separation certificate.  The same-block
    quasi-Schur data supplies the adjacent two-column zero pattern, while the
    spectral obstruction is still an explicit supplied-certificate route. -/
theorem sylvesterTwoColumnBlock_block_and_no_block_action_of_quasiSchur_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      (forall z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        Not (Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z)) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlock_no_block_action_of_complex_disc_det_separation
      m n A T p q hdisc hdetA

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block determinant-shaped complex-separation certificate from a
    negative real discriminant: the square-root `sqrt (-disc)` supplies the
    complex root used by the two-column block determinant bridge, and the
    negative discriminant also forces the subdiagonal coupling `T q p` to be
    nonzero.  The shifted complex determinant separation for `A` remains an
    explicit supplied certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_complex_disc_det_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hdisc :
      (T p p - T q q) ^ 2 + 4 * T p q * T q p < 0)
    (hdetA :
      Not
        ((Matrix.det
          (realMatrixToComplex (Matrix.of A) -
            Matrix.scalar (Fin m)
              (sylvesterTwoColumnRealSchurBlockComplexRoot n T p q
                (Real.sqrt (-((T p p - T q q) ^ 2 + 4 * T p q * T q p))))) = 0))) :
    IsAdjacentQuasiTriangularBlockFn n T p q /\
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  have hcert :=
    sylvesterTwoColumnBlock_block_and_no_block_action_of_quasiSchur_complex_disc_det_separation
      m n A T pmap p q hmono hcard hzero hpq hsame hdisc hdetA
  exact ⟨hcert.1,
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_no_block_action
      m n A T p q hcert.2⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-local
    spectral obstruction for a supplied real `2 x 2` Schur block: a nonzero
    product-shift kernel vector yields two real vectors satisfying the same
    coupled two-column block action, provided the subdiagonal coupling is
    nonzero.  This is the forward algebraic step needed for the real-Schur
    block-separation route: a future separation theorem can rule out these
    coupled block-action witnesses to obtain the product-shift no-eigenvector
    certificate. -/
theorem sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    {u : Fin m -> Real}
    (hker :
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i)) :
    ∃ v : Fin m -> Real,
      Matrix.mulVec (Matrix.of A) u =
          (fun i => T p p * u i + T q p * v i) ∧
      Matrix.mulVec (Matrix.of A) v =
          (fun i => T p q * u i + T q q * v i) := by
  let P : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T p p)
  let Q : Matrix (Fin m) (Fin m) Real :=
    sylvesterTriangularShiftedCoeff m A (T q q)
  let v : Fin m -> Real := fun i => (T q p)⁻¹ * Matrix.mulVec P u i
  refine ⟨v, ?_, ?_⟩
  · funext i
    have hv : T q p * v i = Matrix.mulVec P u i := by
      simp [v, hsub]
    have hP := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T p p) u i
    have hP' : Matrix.mulVec P u i =
        Matrix.mulVec (Matrix.of A) u i - T p p * u i := by
      simpa [P, Matrix.mulVec, dotProduct, Matrix.of_apply] using hP
    calc
      Matrix.mulVec (Matrix.of A) u i =
          Matrix.mulVec P u i + T p p * u i := by linarith
      _ = T p p * u i + T q p * v i := by rw [hv]; ring
  · funext i
    have hQPu : Matrix.mulVec Q (Matrix.mulVec P u) i =
        (T q p * T p q) * u i := by
      have hi := congrFun hker i
      simpa [P, Q, Matrix.mulVec_mulVec] using hi
    have hQv : Matrix.mulVec Q v i = T p q * u i := by
      have hsmul : Matrix.mulVec Q v =
          fun i : Fin m => (T q p)⁻¹ * Matrix.mulVec Q (Matrix.mulVec P u) i := by
        simpa [v] using Matrix.mulVec_smul Q (T q p)⁻¹ (Matrix.mulVec P u)
      calc
        Matrix.mulVec Q v i =
            (T q p)⁻¹ * Matrix.mulVec Q (Matrix.mulVec P u) i := by
              rw [hsmul]
        _ = (T q p)⁻¹ * ((T q p * T p q) * u i) := by rw [hQPu]
        _ = T p q * u i := by
              field_simp [hsub]
    have hQ := sylvesterTriangularShiftedCoeff_mulVec_apply m A (T q q) v i
    have hQ' : Matrix.mulVec Q v i =
        Matrix.mulVec (Matrix.of A) v i - T q q * v i := by
      simpa [Q, Matrix.mulVec, dotProduct, Matrix.of_apply] using hQ
    calc
      Matrix.mulVec (Matrix.of A) v i =
          Matrix.mulVec Q v i + T q q * v i := by linarith
      _ = T p q * u i + T q q * v i := by rw [hQv]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), contrapositive
    block-separation certificate for a supplied real `2 x 2` Schur block: if
    no nonzero vector can be extended to a coupled two-vector block action
    matching the supplied diagonal block, then the product-shift eigen-equation
    has only the zero solution.  Together with the existing
    `sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector`,
    this is the next block-local spectral bridge before a full real-Schur
    separation theorem supplies the `hno` hypothesis from source-level
    spectral disjointness. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    forall u : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i) ->
      u = 0 := by
  intro u hker
  by_contra hune
  exact hno u hune
    (sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
      m n A T p q hsub hker)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), block-action
    separation bridge: if no nonzero concatenated two-column vector can make
    the left `A` action equal the supplied `2 x 2` Schur-block action, then
    the product-shift eigen-equation has only the zero solution.  This is the
    block-matrix target for the still-open spectral-separation proof; it does
    not itself derive separation from eigenvalue disjointness. -/
theorem sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ z : Sum (Fin m) (Fin m) -> Real, z ≠ 0 ->
        ¬ Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) z =
          Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q) z) :
    forall u : Fin m -> Real,
      Matrix.mulVec
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) u =
        (fun i => (T q p * T p q) * u i) ->
      u = 0 := by
  intro u hker
  by_contra hune
  obtain ⟨v, haction⟩ :=
    sylvesterTwoColumnBlock_product_shift_kernel_to_coupled_block_action
      m n A T p q hsub hker
  have hz_ne : Sum.elim u v ≠ 0 := by
    intro hz
    apply hune
    funext i
    have hi := congrFun hz (Sum.inl i)
    simpa using hi
  have hblock :
      Matrix.mulVec (sylvesterTwoColumnBlockLeftAction m A) (Sum.elim u v) =
        Matrix.mulVec (sylvesterTwoColumnBlockSchurAction m n T p q)
          (Sum.elim u v) :=
    (sylvesterTwoColumnBlock_coupled_block_action_iff_leftAction_eq_schurAction
      m n A T p q u v).mp haction
  exact hno (Sum.elim u v) hz_ne hblock

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), real-Schur
    same-block spectral certificate: an adjacent same-labelled block in the
    exported quasi-Schur block map supplies the two-column zero pattern, and a
    supplied no-coupled-action separation condition makes the corresponding
    two-column block coefficient nonsingular.  This is a source-shaped adapter
    for downstream Bartels-Stewart block solves; it still assumes the
    separation/no-action condition rather than proving it from a full real
    Schur spectral theorem. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
    exact
      sylvesterTwoColumnBlockCoeff_product_shift_no_eigenvector_of_no_coupled_block_action
        m n A T p q hsub hno

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), structural
    determinant bridge for a supplied adjacent two-column block with zero
    coupling product: if the two scalar shifted column coefficients
    `A - T_pp I` and `A - T_qq I` are nonsingular and
    `T_qp * T_pq = 0`, then the full two-column block coefficient is
    nonsingular. This instantiates the product-shift quadratic bridge from
    the existing shifted determinant assumptions in the triangular or
    degenerate-block case, avoiding a supplied block inverse/determinant
    certificate for that local step. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  apply sylvesterTwoColumnBlockCoeff_det_ne_zero_of_quadratic_det_ne_zero
    m n A T p q
  · intro hdet
    have hprod :
        Matrix.det
          (sylvesterTriangularShiftedCoeff m A (T q q) *
            sylvesterTriangularShiftedCoeff m A (T p p)) = 0 := by
      simpa [sylvesterTwoColumnBlockFirstQuadraticCoeff, hcouple] using hdet
    rw [Matrix.det_mul] at hprod
    exact (mul_ne_zero hqdet hpdet) hprod
  · intro hdet
    have hcouple' : T p q * T q p = 0 := by
      rw [mul_comm]
      exact hcouple
    have hprod :
        Matrix.det
          (sylvesterTriangularShiftedCoeff m A (T p p) *
            sylvesterTriangularShiftedCoeff m A (T q q)) = 0 := by
      simpa [sylvesterTwoColumnBlockSecondQuadraticCoeff, hcouple'] using hdet
    rw [Matrix.det_mul] at hprod
    exact (mul_ne_zero hpdet hqdet) hprod

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), degenerate
    same-block real-Schur adapter: the exported quasi-Schur block-map data
    supplies the adjacent two-column zero pattern, while nonsingularity of
    the two shifted column coefficients and zero coupling product prove the
    active two-column block coefficient is nonsingular.  This closes the
    zero-coupling subcase of the real `2 x 2` block route; the genuinely
    coupled block still requires a spectral separation/no-coupled-action
    certificate. -/
theorem sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    IsAdjacentQuasiTriangularBlockFn n T p q ∧
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  refine ⟨?_, ?_⟩
  · exact IsAdjacentQuasiTriangularBlockFn.of_quasiSchur_same_block
      n T pmap p q hmono hcard hzero hpq hsame
  · exact sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), right-hand side for
    the supplied adjacent two-column block recurrence.  It collects the
    two active column equations into the same `Sum`-indexed vector space as
    `sylvesterTwoColumnBlockCoeff`; only previously solved columns `j < p`
    appear on this side. -/
def sylvesterTwoColumnBlockRhs (m n : Nat)
    (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n) :
    Sum (Fin m) (Fin m) -> Real :=
  Sum.elim
    (fun i =>
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j))
    (fun i =>
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block recurrence: the block right-hand side depends on `X`
    only through previously solved columns `j < p`. -/
theorem sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq (m n : Nat)
    (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    sylvesterTwoColumnBlockRhs m n T C X p q =
      sylvesterTwoColumnBlockRhs m n T C Y p q := by
  funext r
  cases r with
  | inl i =>
      have hsum :
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j p * X i j) =
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j p * Y i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j < p := (Finset.mem_filter.mp hj).2
        rw [hprev j hjp i]
      simp [sylvesterTwoColumnBlockRhs, hsum]
  | inr i =>
      have hsum :
          Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j q * X i j) =
            Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
              (fun j => T j q * Y i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j < p := (Finset.mem_filter.mp hj).2
        rw [hprev j hjp i]
      simp [sylvesterTwoColumnBlockRhs, hsum]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), exact block-vector form:
    the supplied adjacent two-column predicate is equivalent to one combined
    linear system for the concatenated unknown vector `(Z(:,p), Z(:,q))`.
    This packages the algebra needed by later block-solve/nonsingularity
    statements without claiming those statements here. -/
theorem sylvester_two_column_block_system_iff_blockCoeff_mulVec (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q <->
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
          (Sum.elim (fun i => X i p) (fun i => X i q)) =
        Sum.elim
          (fun i =>
            C i p +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => T j p * X i j))
          (fun i =>
            C i q +
              Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
                (fun j => T j q * X i j)) := by
  constructor
  · intro hsys
    rcases hsys with ⟨hp, hq⟩
    funext r
    cases r with
    | inl i =>
        have hi := congrFun hp i
        rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inl, Pi.add_apply]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        simpa [sub_eq_add_neg, neg_mul] using hi
    | inr i =>
        have hi := congrFun hq i
        rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec]
        simp only [Sum.elim_inr, Pi.add_apply]
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using hi
  · intro hmul
    constructor
    · funext i
      have hi := congrFun hmul (Sum.inl i)
      rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inl, Pi.add_apply] at hi
      rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hi
      simpa [sub_eq_add_neg, neg_mul] using hi
    · funext i
      have hi := congrFun hmul (Sum.inr i)
      rw [sylvesterTwoColumnBlockCoeff, Matrix.fromBlocks_mulVec] at hi
      simp only [Sum.elim_inr, Pi.add_apply] at hi
      rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hi
      simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using hi

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    right-inverse certificate for the two-column block coefficient: if
    `K` is a right inverse of `sylvesterTwoColumnBlockCoeff`, then applying
    `K` to the block right-hand side gives a vector that solves the combined
    two-column linear system. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) =
      sylvesterTwoColumnBlockRhs m n T C X p q := by
  rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block structural certificate: a supplied right inverse of the
    active block coefficient forces the coefficient determinant to be nonzero.
    This is pure exact algebra around the supplied inverse certificate; it does
    not prove that the real-Schur block is nonsingular from spectral separation. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_rightInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  have h := congrArg Matrix.det hRight
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    right-inverse structural certificate: a supplied right inverse makes the
    active block coefficient map onto every right-hand side.  Scope: exact
    supplied-block algebra only, not a proof of the missing quasi-triangular
    block nonsingularity condition. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_rightInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro b
  refine ⟨Matrix.mulVec K b, ?_⟩
  rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    block-vector-to-column wrapper: any vector solving the supplied
    two-column block system yields `IsSylvesterTwoColumnBlockSystem` once
    columns `p` and `q` of `X` are defined by that vector. -/
theorem sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n) (z : Sum (Fin m) (Fin m) -> Real)
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q)
    (hXp : forall i : Fin m, X i p = z (Sum.inl i))
    (hXq : forall i : Fin m, X i q = z (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  apply (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C X p q).mpr
  have hcol :
      Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) = z := by
    funext r
    cases r with
    | inl i => exact hXp i
    | inr i => exact hXq i
  rw [hcol]
  simpa [sylvesterTwoColumnBlockRhs] using hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    right-inverse column wrapper: if columns `p` and `q` of `X` are the
    components of `K` applied to the block right-hand side, and `K` is a
    right inverse of the block coefficient, then `X` satisfies the supplied
    two-column block system. -/
theorem sylvesterTwoColumnBlockSystem_of_rightInverse_columns (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  refine sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector
    m n A T C X p q
    (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) ?_ hXp hXq
  exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
    m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    left-inverse certificate: a supplied left inverse of the two-column
    block coefficient makes its `mulVec` action injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    {x y : Sum (Fin m) (Fin m) -> Real}
    (hxy :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) x =
        Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) y) :
    x = y := by
  have h := congrArg (Matrix.mulVec L) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hLeft, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column block structural certificate: a supplied left inverse of the
    active block coefficient forces the coefficient determinant to be nonzero.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_det_ne_zero_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) := by
  intro hdet
  have h := congrArg Matrix.det hLeft
  rw [Matrix.det_mul, hdet, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block linear algebra wrapper: matching supplied right- and
    left-inverse certificates make the two-column block coefficient map
    bijective.  This packages the finite-dimensional exact algebra that the
    quasi-triangular block nonsingularity row can reuse. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  constructor
  · intro x y hxy
    exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
      m n A T p q L hLeft hxy
  · exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_rightInverse
      m n A T p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block linear solve: if `K` is a supplied right inverse and `L` is a
    supplied left inverse of the same two-column block coefficient, then the
    active block right-hand side has a unique solution vector.  The witness is
    `K` applied to the supplied block right-hand side; uniqueness uses only the
    supplied left-inverse injectivity certificate.  Scope: exact supplied-block
    algebra only; no Schur existence, structural block nonsingularity, or
    floating-point stability is asserted. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  refine ⟨Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q), ?_, ?_⟩
  · exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
      m n A T C X p q K hRight
  · intro z hz
    apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
      m n A T p q L hLeft
    calc
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
          sylvesterTwoColumnBlockRhs m n T C X p q := hz
      _ =
          Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
            (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) := by
            symm
            exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
              m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    active-block solution identification: with matching supplied right- and
    left-inverse certificates, every solution of the active block linear system
    is the vector obtained by applying `K` to the supplied block right-hand
    side.  Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_rightInverse_rhs_of_rightInverse_leftInverse
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z = Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := hz
    _ =
        Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
          (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q)) := by
          symm
          exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
            m n A T C X p q K hRight

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    route for the supplied adjacent two-column block coefficient: a nonzero
    determinant gives Mathlib's nonsingular inverse as a left inverse.  Scope:
    exact supplied-block algebra only; this does not prove real-Schur block
    nonsingularity from spectral separation. -/
theorem sylvesterTwoColumnBlockCoeff_nonsingInv_mul (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q) *
        sylvesterTwoColumnBlockCoeff m n A T p q =
      1 := by
  exact Matrix.nonsing_inv_mul (sylvesterTwoColumnBlockCoeff m n A T p q)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    route for the supplied adjacent two-column block coefficient: a nonzero
    determinant gives Mathlib's nonsingular inverse as a right inverse. -/
theorem sylvesterTwoColumnBlockCoeff_mul_nonsingInv (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    sylvesterTwoColumnBlockCoeff m n A T p q *
        Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q) =
      1 := by
  exact Matrix.mul_nonsing_inv (sylvesterTwoColumnBlockCoeff m n A T p q)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based left action: applying the nonsingular inverse after the
    supplied two-column block coefficient recovers the input vector. -/
theorem sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) =
      z := by
  rw [Matrix.mulVec_mulVec,
    sylvesterTwoColumnBlockCoeff_nonsingInv_mul m n A T p q hdet,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based right action: the supplied two-column block coefficient
    maps the nonsingular-inverse solution of any block right-hand side back to
    that right-hand side. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (rhs : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          rhs) =
      rhs := by
  rw [Matrix.mulVec_mulVec,
    sylvesterTwoColumnBlockCoeff_mul_nonsingInv m n A T p q hdet,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block injectivity: a nonzero determinant of the
    supplied two-column block coefficient makes its `mulVec` action injective.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro x y hxy
  calc
    x =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) x) := by
        symm
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet x
    _ =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) y) := by
        rw [hxy]
    _ = y := by
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet y

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block surjectivity: a nonzero determinant of the
    supplied two-column block coefficient makes its `mulVec` action
    surjective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  intro rhs
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        rhs, ?_⟩
  exact sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    m n A T p q hdet rhs

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block bijectivity wrapper. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) :=
  ⟨sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
      m n A T p q hdet,
    sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
      m n A T p q hdet⟩

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based trivial-kernel wrapper for the supplied two-column block
    coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  constructor
  · intro hz
    calc
      z =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
          symm
          exact
            sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
              m n A T p q hdet z
      _ = 0 := by
          rw [hz]
          exact Matrix.mulVec_zero _
  · intro hz
    rw [hz]
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block linear solve: if the supplied two-column
    block coefficient has nonzero determinant, then the block right-hand side
    has a unique exact solution vector.  The witness is Mathlib's nonsingular
    inverse applied to the supplied block right-hand side. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0)) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q), ?_, ?_⟩
  · exact
      sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
        m n A T p q hdet (sylvesterTwoColumnBlockRhs m n T C X p q)
  · intro z hz
    calc
      z =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
          symm
          exact
            sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
              m n A T p q hdet z
      _ =
          Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
            (sylvesterTwoColumnBlockRhs m n T C X p q) := by
          rw [hz]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    determinant-based active-block solution identification: every vector
    solving the supplied two-column block system equals the nonsingular inverse
    applied to the block right-hand side. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  calc
    z =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z) := by
        symm
        exact
          sylvesterTwoColumnBlockCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero
            m n A T p q hdet z
    _ =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) := by
        rw [hz]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    injectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    surjectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    bijectivity from the bundled real-quasi-Schur block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    unique solve from the bundled real-quasi-Schur block-separation predicate. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), active-block
    solution identification from the bundled real-quasi-Schur
    block-separation predicate. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_realQuasiSchur_block_separation
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hsep : IsSylvesterTwoColumnRealQuasiSchurBlockSeparation m n A T pmap p q)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_realQuasiSchur_block_separation
      m n A T pmap p q hsep).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block injectivity: a trivial kernel for the eigen-equation of the
    product of the two shifted column coefficients makes the supplied
    two-column block `mulVec` action injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block surjectivity: the no-eigenvector product-shift certificate
    makes every supplied two-column block right-hand side reachable. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block bijectivity wrapper for the supplied two-column block. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    trivial-kernel wrapper for the supplied two-column block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block linear solve: the no-eigenvector product-shift certificate
    gives existence and uniqueness for the supplied two-column block right-hand
    side, with witness Mathlib's nonsingular inverse. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    active-block solution identification: any vector solving the supplied
    two-column block system is the nonsingular-inverse solution once the
    product-shift no-eigenvector certificate is available. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block injectivity: an adjacent same-labelled block in a
    supplied quasi-Schur block map, together with the supplied no-coupled-action
    separation condition, makes the two-column block `mulVec` action injective.
    Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block surjectivity: the quasi-Schur/no-coupled-action
    route makes every supplied two-column block right-hand side reachable by
    the block coefficient. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block bijectivity wrapper from the quasi-Schur
    no-coupled-action route. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block trivial-kernel wrapper for the supplied two-column block
    coefficient under the quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i))
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block linear solve: the quasi-Schur/no-coupled-action
    route gives existence and uniqueness for the supplied two-column block
    right-hand side, with witness Mathlib's nonsingular inverse. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block active-block solution identification: any vector solving the
    supplied two-column block system is the nonsingular-inverse solution under
    the quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      ∀ u : Fin m -> Real, u ≠ 0 ->
        ¬ ∃ v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) ∧
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i))
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block injectivity: nonsingular shifted column coefficients and a
    zero coupling product make the supplied two-column block coefficient
    injective.  This is the exact algebraic zero-coupling route, without
    carrying quasi-Schur block-map provenance. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block surjectivity from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block bijectivity from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block trivial-kernel wrapper for the supplied two-column block
    coefficient under shifted determinant and zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block linear solve from nonsingular shifted column coefficients and
    a zero coupling product. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    active-block solution identification under shifted determinant and
    zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block injectivity: same-block quasi-Schur block-map data,
    nonsingular shifted column coefficients, and zero coupling product make the
    supplied two-column block coefficient injective. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_injective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Injective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_injective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block surjectivity from same-block quasi-Schur data,
    nonsingular shifted column coefficients, and zero coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_surjective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block bijectivity wrapper from the same-block
    quasi-Schur/shifted-determinant/zero-coupling route. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_bijective_of_det_ne_zero
    m n A T p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block trivial-kernel wrapper for the supplied two-column block
    coefficient under the same-block quasi-Schur/zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z = 0 <->
      z = 0 := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockCoeff_mulVec_eq_zero_iff_of_det_ne_zero
    m n A T p q hdet z

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block linear solve from same-block quasi-Schur data,
    nonsingular shifted column coefficients, and zero coupling product. -/
theorem existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0) :
    ExistsUnique fun z : Sum (Fin m) (Fin m) -> Real =>
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact existsUnique_sylvesterTwoColumnBlockCoeff_mulVec_of_det_ne_zero
    m n A T C X p q hdet

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block active-block solution identification under same-block
    quasi-Schur data, nonsingular shifted column coefficients, and zero
    coupling product. -/
theorem sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    {z : Sum (Fin m) (Fin m) -> Real}
    (hz :
      Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q) z =
        sylvesterTwoColumnBlockRhs m n T C X p q) :
    z =
      Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
        (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact
    sylvesterTwoColumnBlockCoeff_solutionVector_eq_nonsingInv_rhs_of_det_ne_zero
      m n A T C X p q hdet hz

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant-based
    column wrapper for the supplied adjacent two-column block solve: assigning
    columns `p` and `q` from the nonsingular-inverse block solution makes `X`
    satisfy the supplied two-column block recurrence. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  refine sylvesterTwoColumnBlockSystem_of_blockCoeff_solutionVector
    m n A T C X p q
    (Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
      (sylvesterTwoColumnBlockRhs m n T C X p q)) ?_ hXp hXq
  exact sylvesterTwoColumnBlockCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero
    m n A T p q hdet (sylvesterTwoColumnBlockRhs m n T C X p q)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    column wrapper for the supplied adjacent two-column block solve: assigning
    columns `p` and `q` from the nonsingular-inverse block solution makes `X`
    satisfy the supplied two-column block recurrence once the product-shift
    no-eigenvector certificate is available. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_product_shift_no_eigenvector
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    two-column block inverse consistency: any supplied left inverse and right
    inverse of the same block coefficient coincide.  Scope: exact supplied-block
    algebra only; no Schur existence, structural block nonsingularity, or
    floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    L = K := by
  calc
    L = L * 1 := by rw [mul_one]
    _ = L * (sylvesterTwoColumnBlockCoeff m n A T p q * K) := by rw [hRight]
    _ = (L * sylvesterTwoColumnBlockCoeff m n A T p q) * K := by rw [mul_assoc]
    _ = 1 * K := by rw [hLeft]
    _ = K := by rw [one_mul]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    two-column block solve-vector consistency: applying a supplied left inverse
    or a supplied right inverse to the same active block right-hand side gives
    the same vector.  Scope: exact supplied-block algebra only. -/
theorem sylvesterTwoColumnBlockCoeff_mulVec_leftInverse_rhs_eq_rightInverse_rhs
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1) :
    Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) =
      Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) := by
  have hLK := sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse
    m n A T p q K L hRight hLeft
  simp [hLK]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    left-inverse/right-inverse column wrapper: if columns `p` and `q` of `X`
    are defined by a supplied left inverse, and matching right/left inverse
    certificates are supplied, then `X` satisfies the same two-column block
    system as in the right-inverse wrapper.  Scope: exact supplied-block algebra
    only; no Schur existence, structural block nonsingularity, or floating-point
    stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_of_leftInverse_rightInverse_columns
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec L (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hLK := sylvesterTwoColumnBlockCoeff_leftInverse_eq_rightInverse
    m n A T p q K L hRight hLeft
  refine sylvesterTwoColumnBlockSystem_of_rightInverse_columns
    m n A T C X p q K hRight ?_ ?_
  · intro i
    simpa [hLK] using hXp i
  · intro i
    simpa [hLK] using hXq i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact
    right-inverse/left-inverse bridge for the supplied adjacent two-column
    block system: if `K` is a supplied right inverse of the block coefficient,
    `L` is a supplied left inverse, `Y` solves the supplied block system, and
    the right-hand side source `X` agrees with `Y` on the previous columns
    `j < p`, then the active vector obtained by applying `K` to the `X`-based
    block right-hand side is exactly the active vector of `Y`.  Scope: exact
    supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockCoeff_rightInverse_solutionVector_eq_of_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  have hYm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C Y p q).mp hY
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q))
        = sylvesterTwoColumnBlockRhs m n T C X p q := by
          exact sylvesterTwoColumnBlockCoeff_mulVec_rightInverse_rhs
            m n A T C X p q K hRight
    _ = sylvesterTwoColumnBlockRhs m n T C Y p q := by
          exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq
            m n T C X Y p q hprev
    _ = Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q)) := by
          simpa [sylvesterTwoColumnBlockRhs] using hYm.symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), uniqueness
    wrapper for the supplied two-column block system: if two block-system
    solutions have the same block right-hand side, a supplied left inverse
    forces their active column vectors to be equal. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  apply sylvesterTwoColumnBlockCoeff_mulVec_injective_of_leftInverse
    m n A T p q L hLeft
  have hXm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C X p q).mp hX
  have hYm := (sylvester_two_column_block_system_iff_blockCoeff_mulVec
    m n A T C Y p q).mp hY
  calc
    Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q))
        = sylvesterTwoColumnBlockRhs m n T C X p q := by
          simpa [sylvesterTwoColumnBlockRhs] using hXm
    _ = sylvesterTwoColumnBlockRhs m n T C Y p q := hRhs
    _ = Matrix.mulVec (sylvesterTwoColumnBlockCoeff m n A T p q)
        (Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q)) := by
          simpa [sylvesterTwoColumnBlockRhs] using hYm.symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), component form
    of the left-inverse uniqueness wrapper for supplied two-column block
    systems with the same block right-hand side. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hvec := sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse
    m n A T C X Y p q L hLeft hX hY hRhs
  constructor
  · intro i
    simpa using congrFun hvec (Sum.inl i)
  · intro i
    simpa using congrFun hvec (Sum.inr i)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column recurrence uniqueness bridge: if two block-system solutions
    agree on all previously solved columns `j < p`, then the shared supplied
    left inverse forces their active columns `p` and `q` to agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  apply sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse
    m n A T C X Y p q L hLeft hX hY
  exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq m n T C X Y p q hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    uniqueness wrapper for the supplied two-column block system: a nonzero
    determinant of the supplied block coefficient replaces the separate
    left-inverse certificate when two block systems have the same right-hand
    side.  Scope: exact supplied-block algebra only; this does not prove the
    determinant hypothesis from real-Schur spectral separation. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  exact sylvesterTwoColumnBlockSystem_activeColumns_eq_of_leftInverse
    m n A T C X Y p q
    (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
    (sylvesterTwoColumnBlockCoeff_nonsingInv_mul m n A T p q hdet)
    hX hY hRhs

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), component form
    of the determinant uniqueness wrapper for supplied two-column block systems
    with the same block right-hand side. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hRhs :
      sylvesterTwoColumnBlockRhs m n T C X p q =
        sylvesterTwoColumnBlockRhs m n T C Y p q) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hvec := sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero
    m n A T C X Y p q hdet hX hY hRhs
  constructor
  · intro i
    simpa using congrFun hvec (Sum.inl i)
  · intro i
    simpa using congrFun hvec (Sum.inr i)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    two-column recurrence uniqueness bridge: if two block-system solutions
    agree on all previously solved columns `j < p`, then a nonzero determinant
    of the supplied block coefficient forces their active columns to agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  apply sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero
    m n A T C X Y p q hdet hX hY
  exact sylvesterTwoColumnBlockRhs_eq_of_prev_columns_eq m n T C X Y p q hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the determinant previous-column uniqueness bridge for supplied adjacent
    two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q)
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hX hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), determinant
    nonsingular-inverse solve/uniqueness bridge: if the supplied two-column
    block coefficient has nonzero determinant, columns `p` and `q` of `X` are
    defined by Mathlib's nonsingular inverse applied to the supplied
    `X`-based block right-hand side, and a supplied block-system solution `Y`
    agrees with `X` on the previous columns `j < p`, then the active columns
    agree.  Scope: exact supplied-block algebra only; this does not prove the
    determinant hypothesis from real-Schur spectral separation. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q :=
    sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
      m n A T C X p q hdet hXp hXq
  exact sylvesterTwoColumnBlockSystem_columns_eq_of_det_ne_zero_of_prev_columns_eq
    m n A T C X Y p q hdet hX hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the determinant nonsingular-inverse solve/uniqueness bridge for supplied
    adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), product-shift
    nonsingular-inverse solve/uniqueness bridge: if the supplied two-column
    block columns of `X` are defined by the nonsingular-inverse solve and a
    supplied block-system solution `Y` agrees with `X` on previous columns,
    then the active columns agree under the product-shift no-eigenvector
    certificate. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_product_shift_no_eigenvector
      m n A T p q hker
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the product-shift nonsingular-inverse solve/uniqueness bridge for supplied
    adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (hker :
      forall x : Fin m -> Real,
        Matrix.mulVec
            (sylvesterTriangularShiftedCoeff m A (T q q) *
              sylvesterTriangularShiftedCoeff m A (T p p)) x =
          (fun i => (T q p * T p q) * x i) ->
        x = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_product_shift_no_eigenvector_of_prev_columns_eq
      m n A T C X Y p q hker hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block column wrapper for the supplied adjacent two-column block solve:
    assigning columns `p` and `q` from the nonsingular-inverse block solution
    makes `X` satisfy the supplied two-column block recurrence under the
    quasi-Schur/no-coupled-action hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), real-Schur
    same-block nonsingular-inverse solve/uniqueness bridge: if the supplied
    two-column block columns of `X` are defined by the nonsingular-inverse
    solve and a supplied block-system solution `Y` agrees with `X` on previous
    columns, then the active columns agree under the quasi-Schur/no-coupled
    route. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_no_coupled_block_action
      m n A T pmap p q hmono hcard hzero hpq hsame hsub hno).2
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the real-Schur same-block nonsingular-inverse solve/uniqueness bridge for
    supplied adjacent two-column block systems. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hsub : T q p ≠ 0)
    (hno :
      forall u : Fin m -> Real, u ≠ 0 ->
        Not (exists v : Fin m -> Real,
          Matrix.mulVec (Matrix.of A) u =
              (fun i => T p p * u i + T q p * v i) /\
          Matrix.mulVec (Matrix.of A) v =
              (fun i => T p q * u i + T q q * v i)))
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_no_coupled_block_action_of_prev_columns_eq
      m n A T C X Y pmap p q hmono hcard hzero hpq hsame hsub hno
      hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    column wrapper for the supplied two-column block solve: assigning columns
    `p` and `q` from the nonsingular-inverse block solution makes `X` satisfy
    the supplied two-column recurrence under shifted determinant and
    zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    nonsingular-inverse solve/uniqueness bridge: the shifted determinant and
    zero-coupling route gives active-column uniqueness once previous columns
    agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    sylvesterTwoColumnBlockCoeff_det_ne_zero_of_shifted_det_product_zero
      m n A T p q hpdet hqdet hcouple
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the degenerate nonsingular-inverse solve/uniqueness bridge under shifted
    determinant and zero-coupling hypotheses. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n) (p q : Fin n)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_shifted_det_product_zero_of_prev_columns_eq
      m n A T C X Y p q hpdet hqdet hcouple hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block column wrapper for the supplied adjacent two-column block solve:
    assigning columns `p` and `q` from the nonsingular-inverse block solution
    makes `X` satisfy the supplied two-column recurrence under same-block
    quasi-Schur data, shifted determinant certificates, and zero coupling. -/
theorem sylvesterTwoColumnBlockSystem_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i)) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact sylvesterTwoColumnBlockSystem_of_nonsingInv_columns
    m n A T C X p q hdet hXp hXq

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), degenerate
    same-block nonsingular-inverse solve/uniqueness bridge: the zero-coupling
    quasi-Schur determinant route gives active-column uniqueness once previous
    columns agree. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hdet :
      Not (Matrix.det (sylvesterTwoColumnBlockCoeff m n A T p q) = 0) :=
    (sylvesterTwoColumnBlockCoeff_block_and_det_ne_zero_of_quasiSchur_shifted_det_product_zero
      m n A T pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple).2
  exact
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_det_ne_zero_of_prev_columns_eq
      m n A T C X Y p q hdet hXp hXq hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the degenerate same-block nonsingular-inverse solve/uniqueness bridge. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (pmap : Fin n -> Nat) (p q : Fin n)
    (hmono : Monotone pmap)
    (hcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin n => pmap i = c)).card <= 2)
    (hzero : forall i j : Fin n, pmap j < pmap i -> T i j = 0)
    (hpq : q.val = p.val + 1)
    (hsame : pmap p = pmap q)
    (hpdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T p p)) = 0))
    (hqdet :
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T q q)) = 0))
    (hcouple : T q p * T p q = 0)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec (Inv.inv (sylvesterTwoColumnBlockCoeff m n A T p q))
          (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_nonsingInv_columns_of_quasiSchur_shifted_det_product_zero_of_prev_columns_eq
      m n A T C X Y pmap p q hmono hcard hzero hpq hsame hpdet hqdet hcouple
      hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), exact supplied
    two-column solve/uniqueness bridge: if a supplied right inverse defines
    the active columns of `X` from the block right-hand side, and a supplied
    left inverse gives uniqueness among block-system solutions with the same
    previous columns, then any other supplied block-system solution `Y` that
    agrees with `X` on columns `j < p` has the same active columns.  Scope:
    exact supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_columns_eq_of_rightInverse_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    (forall i : Fin m, X i p = Y i p) /\
      (forall i : Fin m, X i q = Y i q) := by
  have hX : IsSylvesterTwoColumnBlockSystem m n A T C X p q :=
    sylvesterTwoColumnBlockSystem_of_rightInverse_columns
      m n A T C X p q K hRight hXp hXq
  exact sylvesterTwoColumnBlockSystem_columns_eq_of_leftInverse_of_prev_columns_eq
    m n A T C X Y p q L hLeft hX hY hprev

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), vector form of
    the exact supplied two-column solve/uniqueness bridge: under the same
    supplied right-inverse/left-inverse and previous-column agreement
    hypotheses as the component wrapper, the combined active-column vectors
    `(X(:,p), X(:,q))` and `(Y(:,p), Y(:,q))` agree.  Scope: exact
    supplied-block algebra only; no Schur existence, structural block
    nonsingularity, or floating-point stability is asserted. -/
theorem sylvesterTwoColumnBlockSystem_activeColumns_eq_of_rightInverse_leftInverse_prev_columns_eq
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (p q : Fin n)
    (K L : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real)
    (hRight : sylvesterTwoColumnBlockCoeff m n A T p q * K = 1)
    (hLeft : L * sylvesterTwoColumnBlockCoeff m n A T p q = 1)
    (hXp : forall i : Fin m,
      X i p =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inl i))
    (hXq : forall i : Fin m,
      X i q =
        Matrix.mulVec K (sylvesterTwoColumnBlockRhs m n T C X p q) (Sum.inr i))
    (hY : IsSylvesterTwoColumnBlockSystem m n A T C Y p q)
    (hprev : forall j : Fin n, j < p -> forall i : Fin m, X i j = Y i j) :
    Sum.elim (fun i : Fin m => X i p) (fun i : Fin m => X i q) =
      Sum.elim (fun i : Fin m => Y i p) (fun i : Fin m => Y i q) := by
  have hcols :=
    sylvesterTwoColumnBlockSystem_columns_eq_of_rightInverse_leftInverse_prev_columns_eq
      m n A T C X Y p q K L hRight hLeft hXp hXq hY hprev
  funext r
  cases r with
  | inl i => simpa using hcols.1 i
  | inr i => simpa using hcols.2 i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.8), supplied
    quasi-triangular `2 x 2` block recurrence: if columns `p,q` form a supplied
    adjacent diagonal block of the Schur factor `T`, then any exact solution of
    `AX - XT = C` satisfies the simultaneous two-column block system used by
    the real Bartels-Stewart method.  Scope: exact supplied block algebra only;
    this does not assert a real Schur decomposition, block nonsingularity,
    a full Hessenberg-Schur solver, or any floating-point error bound. -/
theorem sylvester_quasiTriangular_two_column_block_system_of_solution
    (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (p q : Fin n)
    (hblock : IsAdjacentQuasiTriangularBlockFn n T p q)
    (hX : IsSylvesterSolutionRect m n A T C X) :
    IsSylvesterTwoColumnBlockSystem m n A T C X p q := by
  rcases hblock with ⟨hpq, hbelowp, hbelowq⟩
  constructor
  · funext i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
    have hop : sylvesterOpRect m n A T X i p =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l p) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j p) := rfl
    have hsum := two_column_block_sum_split m n T X i p q p hpq hbelowp
    have hsol := hX i p
    rw [hop, hsum] at hsol
    show ((Finset.sum Finset.univ fun l : Fin m => A i l * X l p) -
        T p p * X i p) - T q p * X i q =
      C i p +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j p * X i j)
    rw [← hsol]
    ring
  · funext i
    rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
    have hop : sylvesterOpRect m n A T X i q =
        (Finset.sum Finset.univ fun l : Fin m => A i l * X l q) -
          (Finset.sum Finset.univ fun j : Fin n => X i j * T j q) := rfl
    have hsum := two_column_block_sum_split m n T X i p q q hpq hbelowq
    have hsol := hX i q
    rw [hop, hsum] at hsol
    show ((Finset.sum Finset.univ fun l : Fin m => A i l * X l q) -
        T q q * X i q) - T p q * X i p =
      C i q +
        Finset.sum (Finset.filter (fun j => j < p) Finset.univ)
          (fun j => T j q * X i j)
    rw [← hsol]
    ring

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6), pure algebra:
    for upper-triangular `T`, applying the shifted column coefficient to
    column `k` of any `X` splits the Sylvester operator column into the
    already-solved earlier columns,
    `((A - t_kk I) x_k)_i = (AX - XT)_ik + sum_{j<k} t_jk x_ij`.
    The index order and sign follow the module's `sylvesterOpRect`
    orientation `AX - XT`. -/
theorem sylvester_triangular_column_identity (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n) (i : Fin m) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i' => X i' k) i =
      sylvesterOpRect m n A T X i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  rw [sylvesterTriangularShiftedCoeff_mulVec_apply]
  show (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
      T k k * X i k =
    sylvesterOpRect m n A T X i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j)
  have hop : sylvesterOpRect m n A T X i k =
      (Finset.sum Finset.univ fun l : Fin m => A i l * X l k) -
        (Finset.sum Finset.univ fun j : Fin n => X i j * T j k) := rfl
  rw [hop, triangular_column_sum_split m n T hT X i k]
  ring

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    if `X` solves `AX - XT = C` with `T` upper triangular, then column `k`
    of the equation reads
    `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`.
    This is the Bartels-Stewart forward-substitution structure at the
    supplied-triangular level. -/
theorem sylvester_triangular_column_equation (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hX : IsSylvesterSolutionRect m n A T C X) (k : Fin n) :
    Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
        (fun i => X i k) =
      fun i => C i k +
        Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
          (fun j => T j k * X i j) := by
  funext i
  rw [sylvester_triangular_column_identity m n A T X hT k i, hX i k]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6):
    for upper-triangular `T`, solving the rectangular Sylvester equation is
    equivalent to satisfying every Bartels-Stewart column equation. -/
theorem sylvester_triangular_solution_iff_column_equations (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) :
    IsSylvesterSolutionRect m n A T C X <->
      forall k : Fin n,
        Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
            (fun i => X i k) =
          fun i => C i k +
            Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
              (fun j => T j k * X i j) := by
  constructor
  case mp =>
    intro hX k
    exact sylvester_triangular_column_equation m n A T C X hT hX k
  case mpr =>
    intro h i j
    have hj := congrFun (h j) i
    rw [sylvester_triangular_column_identity m n A T X hT j i] at hj
    exact add_right_cancel hj

private theorem mulVec_injective_of_det_ne_zero {m : Nat}
    {M : Matrix (Fin m) (Fin m) Real} (hdet : Not (M.det = 0))
    {x y : Fin m -> Real}
    (hxy : Matrix.mulVec M x = Matrix.mulVec M y) : x = y := by
  have h := congrArg (Matrix.mulVec M⁻¹) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

private theorem mulVec_surjective_of_det_ne_zero {m : Nat}
    {M : Matrix (Fin m) (Fin m) Real} (hdet : Not (M.det = 0))
    (c : Fin m -> Real) :
    exists x : Fin m -> Real, Matrix.mulVec M x = c := by
  refine ⟨Matrix.mulVec M⁻¹ c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    a nonsingular shifted coefficient `A - t I` has Mathlib's nonsingular
    inverse as a left inverse.  This is the exact-arithmetic certificate used
    by the Bartels-Stewart column solve, not a Schur-existence statement. -/
theorem sylvesterTriangularShiftedCoeff_nonsingInv_mul (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    (sylvesterTriangularShiftedCoeff m A t)⁻¹ *
        sylvesterTriangularShiftedCoeff m A t =
      1 := by
  exact Matrix.nonsing_inv_mul (sylvesterTriangularShiftedCoeff m A t)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    a nonsingular shifted coefficient `A - t I` has Mathlib's nonsingular
    inverse as a right inverse. -/
theorem sylvesterTriangularShiftedCoeff_mul_nonsingInv (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    sylvesterTriangularShiftedCoeff m A t *
        (sylvesterTriangularShiftedCoeff m A t)⁻¹ =
      1 := by
  exact Matrix.mul_nonsing_inv (sylvesterTriangularShiftedCoeff m A t)
    (isUnit_iff_ne_zero.mpr hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the map
    `x |-> (A - t I) x` injective. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_injective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Injective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) := by
  intro x y hxy
  exact mulVec_injective_of_det_ne_zero hdet hxy

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the map
    `x |-> (A - t I) x` surjective, so every active column right-hand side is
    reachable in exact arithmetic. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_surjective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Surjective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) := by
  intro c
  exact mulVec_surjective_of_det_ne_zero hdet c

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    nonsingularity of `A - t I` makes the active column solve a bijection. -/
theorem sylvesterTriangularShiftedCoeff_mulVec_bijective (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0)) :
    Function.Bijective
      (Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t)) :=
  ⟨sylvesterTriangularShiftedCoeff_mulVec_injective m A t hdet,
    sylvesterTriangularShiftedCoeff_mulVec_surjective m A t hdet⟩

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column block:
    for every active column right-hand side, the shifted system
    `(A - t I) x = c` has exactly one solution. -/
theorem existsUnique_sylvesterTriangularShiftedCoeff_mulVec (m : Nat)
    (A : RMatFn m m) (t : Real)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A t) = 0))
    (c : Fin m -> Real) :
    ∃! x : Fin m -> Real,
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A t) x = c := by
  have hinj := sylvesterTriangularShiftedCoeff_mulVec_injective m A t hdet
  have hsurj := sylvesterTriangularShiftedCoeff_mulVec_surjective m A t hdet
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column step:
    for supplied upper-triangular `T`, determinant nonsingularity of the shifted
    coefficient `A - t_kk I` gives existence and uniqueness for the exact
    single-column recurrence
    `(A - t_kk I) x_k = c_k + sum_{j<k} t_jk x_j`.
    This is only the supplied-shift column solve certificate; it does not assert
    Schur construction, quasi-triangular block assembly, or floating-point
    stability. -/
theorem existsUnique_sylvester_triangular_column_step_of_shifted_det (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0)) :
    ∃! x : Fin m -> Real,
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) x =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j) := by
  have _ : IsUpperTriangularFn n T := hT
  exact existsUnique_sylvesterTriangularShiftedCoeff_mulVec m A (T k k) hdet
    (fun i => C i k +
      Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
        (fun j => T j k * X i j))

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), active column step:
    under the same shifted determinant nonsingularity, two supplied candidate
    vectors that solve the exact active column equation for the same right-hand
    side must be equal.  This is only a uniqueness consequence for the supplied
    shifted coefficient, not a full Schur assembly or floating-point result. -/
theorem sylvester_triangular_column_step_eq_of_shifted_det (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X : RMatFn m n)
    (hT : IsUpperTriangularFn n T) (k : Fin n)
    (hdet : Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    {x y : Fin m -> Real}
    (hx :
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) x =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j))
    (hy :
      Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) y =
        fun i => C i k +
          Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
            (fun j => T j k * X i j)) :
    x = y := by
  obtain ⟨w, hw, huniq⟩ :=
    existsUnique_sylvester_triangular_column_step_of_shifted_det
      m n A T C X hT k hdet
  exact (huniq x hx).trans (huniq y hy).symm

/-- Higham, 2nd ed., Chapter 16.2, equations (16.5)-(16.6), uniqueness half:
    with upper-triangular `T` and every shifted column coefficient
    `A - t_kk I` nonsingular, two solutions of `AX - XT = C` coincide, by
    strong induction over columns using the column recurrence. -/
theorem sylvester_triangular_solution_unique (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C X Y : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A T C X)
    (hY : IsSylvesterSolutionRect m n A T C Y) :
    X = Y := by
  have hcol : forall N : Nat, forall k : Fin n, k.val < N ->
      (fun i => X i k) = (fun i => Y i k) := by
    intro N
    induction N with
    | zero =>
        intro k hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        intro k hk
        by_cases hlt : k.val < N
        case pos => exact ih k hlt
        case neg =>
          have hXk := sylvester_triangular_column_equation m n A T C X hT hX k
          have hYk := sylvester_triangular_column_equation m n A T C Y hT hY k
          have hrhs :
              (fun i => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * X i j)) =
              (fun i => C i k +
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * Y i j)) := by
            funext i
            have hsum : Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * X i j) =
                Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                  (fun j => T j k * Y i j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : Nat) < (k : Nat) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjN : (j : Nat) < N := by omega
              have hXY : X i j = Y i j := congrFun (ih j hjN) i
              rw [hXY]
            rw [hsum]
          have hmv :
              Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
                  (fun i => X i k) =
                Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k))
                  (fun i => Y i k) := by
            rw [hXk, hYk]
            exact hrhs
          exact mulVec_injective_of_det_ne_zero (hshift k) hmv
  funext i j
  exact congrFun (hcol n j j.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.8), supplied-factor
    Bartels-Stewart existence and uniqueness: with SUPPLIED upper-triangular
    `T` and every shifted column coefficient `A - t_kk I` nonsingular, the
    transformed equation `AX - XT = C` has exactly one solution, built by
    strong induction over columns: column `k` is obtained from the supplied
    inverse of `A - t_kk I` applied to `c_k + sum_{j<k} t_jk x_j` after
    substituting the already-solved earlier columns.  This generalizes the
    diagonal case `existsUnique_isSylvesterSolutionRect_diagonal` of
    `Higham16.lean` to triangular `T`.
    Scope: exact arithmetic at the supplied-factor level; no Schur existence
    (the orthogonal reduction (16.4) is handled separately by
    `sylvester_schur_transform_solution_iff`), no quasi-triangular 2x2
    blocks ((16.7)-(16.8)), and no floating-point error analysis. -/
theorem sylvester_triangular_solve_exists_unique (m n : Nat)
    (A : RMatFn m m) (T : RMatFn n n) (C : RMatFn m n)
    (hT : IsUpperTriangularFn n T)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m A (T k k)) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A T C) := by
  have hpartial : forall N : Nat,
      exists x : Fin n -> Fin m -> Real,
        forall k : Fin n, k.val < N ->
          Matrix.mulVec (sylvesterTriangularShiftedCoeff m A (T k k)) (x k) =
            fun i => C i k +
              Finset.sum (Finset.filter (fun j => j < k) Finset.univ)
                (fun j => T j k * x j i) := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ _ => 0, ?_⟩
        intro k hk
        exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        obtain ⟨x, hx⟩ := ih
        by_cases hN : N < n
        case neg =>
          refine ⟨x, ?_⟩
          intro k hk
          have hkN : k.val < N := by
            have hkn : k.val < n := k.isLt
            omega
          exact hx k hkN
        case pos =>
          obtain ⟨xk, hxk⟩ :=
            mulVec_surjective_of_det_ne_zero (hshift ⟨N, hN⟩)
              (fun i => C i ⟨N, hN⟩ +
                Finset.sum
                  (Finset.filter (fun j => j < (⟨N, hN⟩ : Fin n)) Finset.univ)
                  (fun j => T j ⟨N, hN⟩ * x j i))
          refine ⟨Function.update x ⟨N, hN⟩ xk, ?_⟩
          intro k hk
          have hupdate_rhs : forall k' : Fin n, k'.val <= N ->
              (fun i => C i k' +
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * Function.update x ⟨N, hN⟩ xk j i)) =
              (fun i => C i k' +
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * x j i)) := by
            intro k' hk'
            funext i
            have hsum : Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * Function.update x ⟨N, hN⟩ xk j i) =
                Finset.sum (Finset.filter (fun j => j < k') Finset.univ)
                  (fun j => T j k' * x j i) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : Nat) < (k' : Nat) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjne : Not (j = (⟨N, hN⟩ : Fin n)) := by
                intro hje
                have hjval : (j : Nat) = N := by rw [hje]
                omega
              rw [Function.update_of_ne hjne]
            rw [hsum]
          by_cases hkval : k.val < N
          case pos =>
            have hkne : Not (k = (⟨N, hN⟩ : Fin n)) := by
              intro hke
              have hkv : (k : Nat) = N := by rw [hke]
              omega
            rw [Function.update_of_ne hkne,
              hupdate_rhs k (Nat.le_of_lt hkval)]
            exact hx k hkval
          case neg =>
            have hkeq : k = (⟨N, hN⟩ : Fin n) := by
              apply Fin.ext
              show (k : Nat) = N
              omega
            rw [hkeq, Function.update_self,
              hupdate_rhs ⟨N, hN⟩ (Nat.le_refl N)]
            exact hxk
  obtain ⟨x, hx⟩ := hpartial n
  have hsol : IsSylvesterSolutionRect m n A T C (fun i j => x j i) := by
    apply (sylvester_triangular_solution_iff_column_equations m n A T C
      (fun i j => x j i) hT).mpr
    intro k
    exact hx k k.isLt
  refine ⟨fun i j => x j i, hsol, ?_⟩
  intro Y hY
  exact sylvester_triangular_solution_unique m n A T C Y (fun i j => x j i)
    hT hshift hY hsol

private theorem rectMatMul_schur_coords_expand_for_triangular {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul U
      (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)) = C := by
  have hUUt : rectMatMul U (matTranspose U) = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.right_inv i j
  have hVVt : rectMatMul V (matTranspose V) = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.right_inv i j
  calc
    rectMatMul U
        (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V))
        = rectMatMul (rectMatMul U
            (rectMatMul (matTranspose U) (rectMatMul C V))) (matTranspose V) := by
            exact (rectMatMul_assoc U
              (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)).symm
    _ = rectMatMul (rectMatMul (rectMatMul U (matTranspose U))
            (rectMatMul C V)) (matTranspose V) := by
            exact congrArg (fun Z => rectMatMul Z (matTranspose V))
              (rectMatMul_assoc U (matTranspose U) (rectMatMul C V)).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul C V)) (matTranspose V) := by
            rw [hUUt]
    _ = rectMatMul (rectMatMul C V) (matTranspose V) := by
            rw [rectMatMul_id_left]
    _ = rectMatMul C (rectMatMul V (matTranspose V)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul C (idMatrix n) := by
            rw [hVVt]
    _ = C := by
            rw [rectMatMul_id_right]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), supplied Schur
    triangular solve: if orthogonal supplied factors put `A` and `B` into
    coordinates `R` and upper-triangular `S`, and every shifted column
    coefficient `R - s_kk I` is nonsingular, then the original-coordinate
    equation `AX - XB = C` has exactly one solution.  This composes the
    supplied-factor Schur equivalence `sylvester_schur_transform_solution_iff`
    with the Bartels-Stewart column solve `sylvester_triangular_solve_exists_unique`.
    Scope: exact arithmetic only; Schur existence, real quasi-triangular 2x2
    blocks, Hessenberg-Schur reductions, and floating-point stability remain
    separate open rows. -/
theorem existsUnique_isSylvesterSolutionRect_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  let Cschur : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  obtain ⟨Y, hY, hYuniq⟩ :=
    sylvester_triangular_solve_exists_unique m n R S Cschur hS hshift
  refine ⟨rectMatMul U (rectMatMul Y (matTranspose V)), ?_, ?_⟩
  · exact (sylvester_schur_transform_solution_iff m n
      U R A V S B C Y hU hV hA hB).mpr hY
  · intro X hX
    let YX : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul X V)
    have hXexpand : rectMatMul U (rectMatMul YX (matTranspose V)) = X :=
      rectMatMul_schur_coords_expand_for_triangular U V X hU hV
    have hXsol :
        IsSylvesterSolutionRect m n A B C
          (rectMatMul U (rectMatMul YX (matTranspose V))) := by
      rw [hXexpand]
      exact hX
    have hYX :
        IsSylvesterSolutionRect m n R S Cschur YX :=
      (sylvester_schur_transform_solution_iff m n
        U R A V S B C YX hU hV hA hB).mp hXsol
    have hYeq : YX = Y := hYuniq YX hYX
    calc
      X = rectMatMul U (rectMatMul YX (matTranspose V)) := hXexpand.symm
      _ = rectMatMul U (rectMatMul Y (matTranspose V)) := by rw [hYeq]

/-- Real quasi-Schur-to-triangular uniqueness bridge.  The theorem returns the
    exact real quasi-Schur factors for `A` and `B`; if the returned `B`-side
    block map is supplied to be strictly increasing down the matrix order, so
    the selected Schur factor is effectively upper triangular, and each
    shifted triangular column coefficient is nonsingular, then the original
    Sylvester equation has a unique exact solution.

    Scope: exact arithmetic and the triangular subcase only.  This deliberately
    does not claim full quasi-triangular block nonsingularity, Hessenberg-Schur
    execution, or floating-point stability. -/
theorem existsUnique_isSylvesterSolutionRect_realQuasiSchur_of_strictBlockMap
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n) (C : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        ExistsUnique (IsSylvesterSolutionRect m n A B C)) := by
  obtain ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff
      m n A B C (0 : RMatFn m n)
  refine ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, ?_⟩
  intro hpBstrict hshift
  have hS : IsUpperTriangularFn n S :=
    IsUpperTriangularFn.of_quasiSchur_strictBlockMap n S pB hSzero hpBstrict
  exact
    existsUnique_isSylvesterSolutionRect_schurTriangular
      m n U R A V S B C hU hV hA hB hS hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: supplied orthogonal factors,
    an upper-triangular transformed `S`, and nonsingular shifted column
    coefficients make the vectorized Sylvester coefficient have trivial
    kernel.  Scope: supplied exact factors only; this does not assert Schur
    existence or floating-point stability. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_eq_zero_iff (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 <->
      X = 0 := by
  constructor
  case mp =>
    intro h
    have hsol : IsSylvesterSolutionRect m n A B (0 : RMatFn m n) X :=
      (sylvester_vec_system_iff_solution m n A B (0 : RMatFn m n) X).mp
        (by simpa using h)
    have hzero : IsSylvesterSolutionRect m n A B
        (0 : RMatFn m n) (0 : RMatFn m n) := by
      apply (sylvester_vec_system_iff_solution m n A B
        (0 : RMatFn m n) (0 : RMatFn m n)).mp
      change Matrix.mulVec (sylvesterVecCoeff m n A B)
          (0 : Prod (Fin n) (Fin m) -> Real) = 0
      exact Matrix.mulVec_zero _
    obtain ⟨Y, hY, hYuniq⟩ :=
      existsUnique_isSylvesterSolutionRect_schurTriangular m n
        U R A V S B (0 : RMatFn m n) hU hV hA hB hS hshift
    have hXY : X = Y := hYuniq X hsol
    have h0Y : (0 : RMatFn m n) = Y := hYuniq (0 : RMatFn m n) hzero
    rw [hXY, ← h0Y]
  case mpr =>
    intro hX
    rw [hX]
    change Matrix.mulVec (sylvesterVecCoeff m n A B)
        (0 : Prod (Fin n) (Fin m) -> Real) = 0
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is injective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_injective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro x y hxy
  let P := sylvesterVecCoeff m n A B
  have hker : Matrix.mulVec P (x - y) = 0 := by
    dsimp [P]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  obtain ⟨X, hXvec⟩ :=
    Matrix.vec_bijective.surjective (x - y : Prod (Fin n) (Fin m) -> Real)
  have hkerX :
      Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 := by
    dsimp [P] at hker
    rw [hXvec]
    exact hker
  have hXzero : X = 0 :=
    (sylvesterVecCoeff_schurTriangular_mulVec_eq_zero_iff
      m n U R A V S B X hU hV hA hB hS hshift).mp hkerX
  have hsub : x - y = 0 := by
    rw [← hXvec, hXzero]
    rfl
  exact sub_eq_zero.mp hsub

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is surjective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_surjective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro y
  obtain ⟨C, hC⟩ := Matrix.vec_bijective.surjective y
  obtain ⟨X, hX, _⟩ :=
    existsUnique_isSylvesterSolutionRect_schurTriangular m n
      U R A V S B C hU hV hA hB hS hshift
  refine ⟨Matrix.vec X, ?_⟩
  rw [← hC]
  exact (sylvester_vec_system_iff_solution m n A B C X).mpr hX

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    coefficient is bijective under the exact supplied-factor assumptions. -/
theorem sylvesterVecCoeff_schurTriangular_mulVec_bijective (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift,
    sylvesterVecCoeff_schurTriangular_mulVec_surjective
      m n U R A V S B hU hV hA hB hS hshift⟩

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vectorized Sylvester
    linear system has a unique solution for every vectorized right-hand side
    under the exact supplied-factor assumptions. -/
theorem existsUnique_sylvesterVecCoeff_schurTriangular_mulVec (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift
  have hsurj :=
    sylvesterVecCoeff_schurTriangular_mulVec_surjective
      m n U R A V S B hU hV hA hB hS hshift
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6),
    supplied triangular Schur-coordinate case: the vec/Kronecker Sylvester
    coefficient itself is nonsingular under the exact supplied-factor
    assumptions.  This records the determinant form corresponding to the
    bijective vectorized solve above; it is still a supplied-factor result,
    not a proof of Schur existence or floating-point stability. -/
theorem sylvesterVecCoeff_schurTriangular_det_ne_zero (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  intro hdet
  obtain ⟨x, hxne, hxzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hinj :=
    sylvesterVecCoeff_schurTriangular_mulVec_injective
      m n U R A V S B hU hV hA hB hS hshift
  have hxzero' : x = 0 := by
    apply hinj
    rw [hxzero, Matrix.mulVec_zero]
  exact hxne hxzero'

/-- Higham, 2nd ed., Chapter 16.2, equation (16.4), strict singleton-block
    specialization of the supplied real quasi-Schur block map: if the supplied
    block map strictly increases with the matrix index, then the quasi-Schur
    below-block zero condition is ordinary upper triangularity. -/
theorem isUpperTriangularFn_of_strictBlockMap (n : Nat)
    (S : RMatFn n n) (p : Fin n -> Nat)
    (hpstrict : forall {i j : Fin n}, j < i -> p j < p i)
    (hSstrict : forall i j : Fin n, p j < p i -> S i j = 0) :
    IsUpperTriangularFn n S := by
  intro i j hji
  exact hSstrict i j (hpstrict hji)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    `B`-side singleton-block real-quasi-Schur case: supplied orthogonal
    factors, a strictly increasing `B`-side block map, and nonsingular shifted
    column coefficients make the original vec/Kronecker Sylvester coefficient
    nonsingular.  This is the minimal strict-block-map determinant surface; no
    left block-map data is needed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  exact
    sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB
      (isUpperTriangularFn_of_strictBlockMap n S pB hpBstrict hSstrict)
      hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: supplied real quasi-Schur factors
    whose `B`-side block map is strictly increasing reduce to the supplied
    Schur-triangular determinant theorem, so the original vec/Kronecker
    Sylvester coefficient is nonsingular. Scope: exact supplied factors only;
    this does not prove the 2-by-2 real quasi-Schur block solve or floating-
    point Bartels-Stewart stability. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  exact
    sylvesterVecCoeff_realQuasiSchur_strictBBlockMap_det_ne_zero
      m n U R A V S B pB hU hV hA hB hpBstrict hSstrict hshift

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient have
    trivial kernel. Scope: exact supplied factors only; no 2-by-2 block solve
    or floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_eq_zero_iff
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) x = 0 <-> x = 0 := by
  constructor
  · intro hx
    have hdet :=
      sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
        m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
        hpBmono hpBcard hpBstrict hSstrict hshift
    have h := congrArg
      (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))) hx
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec] at h
    exact h
  · intro hx
    rw [hx]
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient
    injective. Scope: exact supplied factors only; no 2-by-2 block solve or
    floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  intro x y hxy
  have h := congrArg
    (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the strict supplied-factor
    determinant certificate makes the vectorized Sylvester coefficient
    surjective, so every vectorized right-hand side is reachable in exact
    arithmetic. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  intro c
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the vectorized Sylvester
    coefficient solve is bijective under the exact supplied-factor
    assumptions. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_bijective
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift,
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift⟩

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: every vectorized right-hand side
    has a unique exact solution under the strict supplied-factor assumptions. -/
theorem existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_injective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  have hsurj :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_mulVec_surjective
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: Mathlib's nonsingular inverse gives
    an explicit exact vectorized Sylvester coefficient solution for any right-
    hand side. Scope: supplied exact factors only; no 2-by-2 block solve or
    floating-point stability is claimed. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff m n A B)
        (Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c) =
      c := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the nonsingular inverse is a left
    action on the vectorized Sylvester coefficient under the supplied exact
    factor hypotheses. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (x : Prod (Fin n) (Fin m) -> Real) :
    Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))
        (Matrix.mulVec (sylvesterVecCoeff m n A B) x) =
      x := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
      (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: any exact vectorized Sylvester
    coefficient solution is the nonsingular-inverse solution. -/
theorem sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    {x c : Prod (Fin n) (Fin m) -> Real}
    (hx : Matrix.mulVec (sylvesterVecCoeff m n A B) x = c) :
    x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  calc
    x =
        Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B))
          (Matrix.mulVec (sylvesterVecCoeff m n A B) x) := by
        symm
        exact
          sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_mulVec
            m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
            hpBmono hpBcard hpBstrict hSstrict hshift x
    _ = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
        rw [hx]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.6), strict
    real-quasi-Schur singleton-block case: the nonsingular-inverse formula is
    the unique exact vectorized Sylvester coefficient solution for the supplied
    factors. -/
theorem existsUnique_sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c ∧
        x = Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c := by
  refine
    ⟨Matrix.mulVec (Inv.inv (sylvesterVecCoeff m n A B)) c, ?_, ?_⟩
  · exact
      ⟨sylvesterVecCoeff_realQuasiSchur_strictBlockMap_nonsingInv_mulVec_solution
          m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
          hpBmono hpBcard hpBstrict hSstrict hshift c,
        rfl⟩
  · intro y hy
    exact
      sylvesterVecCoeff_realQuasiSchur_strictBlockMap_eq_nonsingInv_mulVec_of_mulVec_eq
        m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
        hpBmono hpBcard hpBstrict hSstrict hshift hy.1

/-- Higham, 2nd ed., Chapter 16.1-16.2, equation (16.3), strict
    real-quasi-Schur singleton-block nonsingularity excludes a supplied common
    real right/transpose eigenpair of `A` and `B`. -/
theorem no_common_real_eigenpair_of_realQuasiSchur_strictBlockMap (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.mulVec (Matrix.transpose B) w = fun j => lam * w j) :
    False := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  exact hdet
    (sylvesterVecCoeff_singular_of_common_eigenvalue
      m n A B v w lam hv0 hw0 hv hw)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equation (16.3), strict
    real-quasi-Schur singleton-block nonsingularity excludes a supplied common
    real right/left eigenpair of `A` and `B`. -/
theorem no_common_real_left_eigenpair_of_realQuasiSchur_strictBlockMap
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hpBstrict : forall {i j : Fin n}, j < i -> pB j < pB i)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real)
    (hv0 : Not (v = 0)) (hw0 : Not (w = 0))
    (hv : Matrix.mulVec A v = fun i => lam * v i)
    (hw : Matrix.vecMul w B = fun j => lam * w j) :
    False := by
  have hdet :=
    sylvesterVecCoeff_realQuasiSchur_strictBlockMap_det_ne_zero
      m n U R A V S B pA pB hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hpBstrict hSstrict hshift
  apply hdet
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Matrix.vec (fun i j => v i * w j : RMatFn m n),
    vec_outer_product_ne_zero m n v w hv0 hw0, ?_⟩
  rw [sylvesterVecCoeff_eigenpair_vecMul m n A B v w lam lam hv hw]
  funext p
  simp

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6),
    supplied triangular Schur-coordinate case: the exact shifted-determinant
    hypotheses that make the vectorized Sylvester coefficient nonsingular also
    rule out supplied common real eigenpairs of `A` and `B^T`. -/
theorem no_common_real_eigenpair_of_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.mulVec (Matrix.transpose B) w = (fun j => lam * w j)) :=
  no_common_real_eigenpair_of_sylvesterVecCoeff_det_ne_zero m n A B
    (sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB hS hshift)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6),
    supplied triangular Schur-coordinate case in left-eigenvector form:
    exact shifted-determinant hypotheses rule out supplied nonzero real
    eigenpairs `A v = lam v` and `w^T B = lam w^T`. -/
theorem no_common_real_left_eigenpair_of_schurTriangular (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) :
    Not (∃ (v : Fin m -> Real) (w : Fin n -> Real) (lam : Real),
      Not (v = 0) ∧ Not (w = 0) ∧
        Matrix.mulVec A v = (fun i => lam * v i) ∧
        Matrix.vecMul w B = (fun j => lam * w j)) :=
  no_common_real_left_eigenpair_of_sylvesterVecCoeff_det_ne_zero m n A B
    (sylvesterVecCoeff_schurTriangular_det_ne_zero
      m n U R A V S B hU hV hA hB hS hshift)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case: the practical componentwise error bound can use
    the actual nonsingular inverse of the vec/Kronecker Sylvester coefficient.
    The supplied Schur-triangular hypotheses prove the left-inverse condition
    for `P^{-1}`, while the residual-budget certificate remains explicit.
    Scope: exact supplied factors only; this does not assert Schur existence,
    a LAPACK estimator, or a full floating-point solution algorithm. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with componentwise larger practical-budget inputs.
    The exact nonsingular inverse is supplied by the Schur-triangular
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` are merely larger
    estimator inputs.  Scope: exact supplied factors only; this does not assert
    Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions:
    nonnegative componentwise residual tolerances and an entrywise computed
    residual error bound supply the practical componentwise error bound. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      ⟨hRu, hRhat⟩ hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), real quasi-Schur
    triangular subcase: return exact real quasi-Schur factors for `A` and `B`;
    if the returned `B`-side block labels are strictly increasing below the
    diagonal and the shifted triangular column coefficients are nonsingular,
    then the raw computed-residual practical bound follows for the original
    `A` and `B`.

    Scope: this is only the strict-block-map triangular subcase, reusing the
    supplied Schur-triangular endpoint above.  It does not assert full
    quasi-triangular block nonsingularity, Hessenberg-Schur execution, rounded
    residual arithmetic, or floating-point stability. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        IsSylvesterSolutionRect m n A B C X ->
        (∀ i j, 0 <= Ru i j) ->
        (∀ i j,
          |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) ->
        0 < sylvesterMaxEntryNormRect m n Xhat ->
        sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
            sylvesterMaxEntryNormRect m n Xhat <=
          sylvesterVecMaxNorm m n
            (sylvesterPracticalBudgetVec m n
              (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
            sylvesterMaxEntryNormRect m n Xhat) := by
  obtain ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, _hiff⟩ :=
    sylvester_realQuasiSchur_transform_solution_iff
      m n A B C (0 : RMatFn m n)
  refine ⟨U, R, V, S, pA, pB,
    hU, hV, hA, hB, hpAmono, hpAcard, hRzero,
    hpBmono, hpBcard, hSzero, ?_⟩
  intro hpBstrict hshift hX hRu hRhat hXhat
  have hS : IsUpperTriangularFn n S :=
    IsUpperTriangularFn.of_quasiSchur_strictBlockMap n S pB hSzero hpBstrict
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate. The strict block-map hypotheses are supplied factors, while
    vec/Kronecker nonsingularity remains an explicit determinant certificate. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate and componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with a packaged computed-residual budget
    certificate, monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model:
    package `Rhat = R(Xhat) + dR` and `|dR| <= Ru` as a computed-residual
    certificate, then use the supplied strict-block certificate. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
      m n U R A V S B pA pB C X Xhat Rhat Ru
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model
    and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
      m n U R A V S B pA pB C X Xhat Rhat Ru eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model and
    componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with an explicit residual error model and
    a monotone scalar cap on an estimated practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
      m n U R A V S B pA pB C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions and a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_scalar m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions and componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hRu hRhat hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case with raw computed-residual budget
    assumptions, monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have _hU := hU
  have _hV := hV
  have _hA := hA
  have _hB := hB
  have _hpAmono := hpAmono
  have _hpAcard := hpAcard
  have _hRstrict := hRstrict
  have _hpBmono := hpBmono
  have _hpBcard := hpBcard
  have _hSstrict := hSstrict
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hRu hRhat hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions and
    componentwise larger practical-budget inputs. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hS hshift hX ⟨hRu, hRhat⟩
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model:
    if `Rhat = R(Xhat) + dR` and `|dR| <= Ru`, then the practical
    componentwise error bound follows using the nonsingular inverse of the
    supplied Schur-triangular vec/Kronecker coefficient. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
      m n U R A V S B C X Xhat Rhat Ru hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and
    componentwise larger practical-budget inputs.  This remains an exact
    supplied-factor wrapper: no Schur existence, rounded residual arithmetic,
    or estimator proof is asserted. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with a scalar cap on the nonsingular-inverse
    practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with a monotone scalar cap on an estimated practical
    budget.  The exact nonsingular inverse is supplied by the Schur-triangular
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise
    larger estimator inputs. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurTriangular_det_ne_zero
            m n U R A V S B hU hV hA hB hS hshift)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions and a
    scalar cap on the nonsingular-inverse practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
      m n U R A V S B C X Xhat Rhat Ru eta hU hV hA hB hS hshift hX
      ⟨hRu, hRhat⟩ heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with raw computed-residual budget assumptions,
    monotone supplied estimates, and a scalar cap. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hS hshift hX ⟨hRu, hRhat⟩
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and a scalar
    cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
      m n U R A V S B C X Xhat Rhat Ru eta hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case with an explicit residual error model and a monotone
    scalar cap on an estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
      m n U R A V S B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hS hshift hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_budget_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_schurTriangular_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_schurTriangular_computed_residual_error_model_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_certificate
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_budget
    (m n : Nat) (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n) :
    ∃ (U R : RMatFn m m) (V S : RMatFn n n)
      (pA : Fin m -> Nat) (pB : Fin n -> Nat),
      IsOrthogonal m U ∧
      IsOrthogonal n V ∧
      A = rectMatMul U (rectMatMul R (matTranspose U)) ∧
      B = rectMatMul V (rectMatMul S (matTranspose V)) ∧
      Monotone pA ∧
      (∀ c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2) ∧
      (∀ i j : Fin m, pA j < pA i -> R i j = 0) ∧
      Monotone pB ∧
      (∀ c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2) ∧
      (∀ i j : Fin n, pB j < pB i -> S i j = 0) ∧
      ((∀ i j : Fin n, j < i -> pB j < pB i) ->
        (∀ k : Fin n,
          Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0)) ->
        IsSylvesterSolutionRect m n A B C X ->
        (∀ i j, 0 <= Ru i j) ->
        (∀ i j,
          |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) ->
        0 < sylvesterMaxEntryNormRect m n Xhat ->
        sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
            sylvesterMaxEntryNormRect m n Xhat <=
          sylvesterVecMaxNorm m n
            (sylvesterPracticalBudgetVec m n
              (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
            sylvesterMaxEntryNormRect m n Xhat) := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget
      m n A B C X Xhat Rhat Ru

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_budget_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_budget_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_budget_mono_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_error_model_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_scalar
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono
  all_goals assumption

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for this practical Sylvester residual error bound endpoint. -/
theorem H16_eq16_29_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  apply sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_error_model_mono_scalar
  all_goals assumption

end LeanFpAnalysis.FP
