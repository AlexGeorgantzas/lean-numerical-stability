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
-- * The CONVERSE direction of (16.3) -- every eigenvalue of the Kronecker
--   coefficient is a difference `lam_i(A) - mu_j(B)`, hence nonsingularity
--   FROM the absence of common eigenvalues -- needs simultaneous unitary
--   triangularization (Schur form) over the complex numbers, which Mathlib
--   does not currently provide; it remains open here.  This module works
--   over the reals, so only real eigenpairs are covered; complex-conjugate
--   eigenvalue pairs of real matrices are outside the statements below.
-- * The quasi-triangular (2x2 diagonal block, real-Schur) Bartels-Stewart
--   variant behind equations (16.7)-(16.8) is not implemented; only the
--   strictly (upper-)triangular column solve is formalized.
-- * No Schur existence, no floating-point rounding analysis: all triangular
--   and eigenpair data are supplied hypotheses, exactly as in the
--   supplied-factor diagonal case of `Higham16.lean`.

import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace LeanFpAnalysis.FP

open scoped BigOperators

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

end LeanFpAnalysis.FP
