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

end LeanFpAnalysis.FP
